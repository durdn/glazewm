// The `windows` or `console` subsystem (default is `console`) determines
// whether a console window is spawned on launch, if not already ran
// through a console. The following prevents this additional console window
// in release mode.
#![cfg_attr(
  all(not(debug_assertions), target_os = "windows"),
  windows_subsystem = "windows"
)]
#![warn(clippy::all, clippy::pedantic)]
#![feature(iterator_try_collect)]

#[cfg(target_os = "macos")]
use std::io::IsTerminal;
use std::{env, io::Write, path::PathBuf, process, time::Duration};

use anyhow::{Context, Error};
use tokio::{process::Command, signal};
use tracing::Level;
use tracing_subscriber::{
  fmt::{self, writer::MakeWriterExt},
  layer::SubscriberExt,
};
use wm_common::{AppCommand, InvokeCommand, Verbosity, WmEvent};
#[cfg(target_os = "macos")]
use wm_platform::DispatcherExtMacOs;
use wm_platform::{
  Dispatcher, DisplayListener, EventLoop, KeybindingListener,
  MouseEventKind, MouseListener, PlatformEvent, SingleInstance,
  WindowListener,
};

use crate::{
  ipc_server::IpcServer, sys_tray::SystemTray, traits::CommonGetters,
  user_config::UserConfig, wm::WindowManager, wm_state::WmState,
};

mod commands;
mod events;
mod ipc_server;
mod models;
mod pending_sync;
mod sys_tray;
mod traits;
mod user_config;
mod wm;
mod wm_state;

/// Installs a panic hook that writes directly to `errors.log` before the
/// process aborts. Writing directly to disk (not via tracing) is critical
/// — tracing's buffered writer may not flush before abort.
fn install_panic_hook() {
  std::panic::set_hook(Box::new(|info| {
    let log_path = home::home_dir().map_or_else(
      || std::path::PathBuf::from("errors.log"),
      |h| h.join(".glzr/glazewm/errors.log"),
    );

    if let Ok(mut file) = std::fs::OpenOptions::new()
      .create(true)
      .append(true)
      .open(&log_path)
    {
      let _ = writeln!(file, "PANIC: {info}");
      let _ = file.flush();
    }
  }));
}

/// Logs committed and working-set memory, system available RAM, and key
/// container counts.
///
/// Written directly to `errors.log` (unbuffered), bypassing the tracing
/// buffer so the line is on disk even if the process aborts immediately
/// after. Fields:
/// - `avail=` — free physical RAM (low = system memory pressure)
/// - `avail_page=` — available commit charge / page file headroom (low =
///   allocations fail even with free physical RAM)
/// - `avail_virt=` — available virtual address space in this process (low
///   = VA exhaustion, allocations fail regardless of physical/page file)
fn log_memory_diagnostics(state: &WmState) {
  #[cfg(target_os = "windows")]
  if let Some((ws_mb, commit_mb)) = memory_mb() {
    let (avail_mb, avail_page_mb, avail_virt_mb) =
      system_avail_mb().unwrap_or((0, 0, 0));
    let mon = state.monitors().len();
    let ws = state.workspaces().len();
    let win = state.windows().len();
    let tree = state.root_container.descendants().count();
    let ign = state.ignored_windows.len();
    let ghosts = state.disconnected_monitors.len();

    let log_path = home::home_dir().map_or_else(
      || std::path::PathBuf::from("errors.log"),
      |h| h.join(".glzr/glazewm/errors.log"),
    );

    if let Ok(mut file) = std::fs::OpenOptions::new()
      .create(true)
      .append(true)
      .open(&log_path)
    {
      let _ = writeln!(
        file,
        "MEM: ws={ws_mb}MB commit={commit_mb}MB avail={avail_mb}MB \
         avail_page={avail_page_mb}MB avail_virt={avail_virt_mb}MB \
         | mon={mon} ws={ws} win={win} tree={tree} ign={ign} \
         ghosts={ghosts}"
      );
      let _ = file.flush();
    }
  }
}

/// Returns `(working_set_mb, committed_mb)` for the current process.
///
/// `working_set_size` reflects only RAM-resident pages; `pagefile_usage`
/// (committed virtual memory) is the true allocation metric and includes
/// pages currently backed by the pagefile.
#[cfg(target_os = "windows")]
fn memory_mb() -> Option<(usize, usize)> {
  // SAFETY: Declare the Win32 APIs needed for memory diagnostics.
  // `GetCurrentProcess` returns a pseudo-handle that is always valid.
  // `K32GetProcessMemoryInfo` fills `pmc` on success (non-zero return).
  #[repr(C)]
  #[allow(non_snake_case, non_camel_case_types)]
  struct PROCESS_MEMORY_COUNTERS {
    cb: u32,
    PageFaultCount: u32,
    PeakWorkingSetSize: usize,
    WorkingSetSize: usize,
    QuotaPeakPagedPoolUsage: usize,
    QuotaPagedPoolUsage: usize,
    QuotaPeakNonPagedPoolUsage: usize,
    QuotaNonPagedPoolUsage: usize,
    PagefileUsage: usize,
    PeakPagefileUsage: usize,
  }

  extern "system" {
    fn GetCurrentProcess() -> isize;
    fn K32GetProcessMemoryInfo(
      process: isize,
      pmc: *mut PROCESS_MEMORY_COUNTERS,
      cb: u32,
    ) -> i32;
  }

  unsafe {
    let handle = GetCurrentProcess();
    let mut pmc = std::mem::zeroed::<PROCESS_MEMORY_COUNTERS>();
    pmc.cb = u32::try_from(std::mem::size_of::<PROCESS_MEMORY_COUNTERS>())
      .unwrap_or_default();

    if K32GetProcessMemoryInfo(handle, &raw mut pmc, pmc.cb) != 0 {
      Some((
        pmc.WorkingSetSize / (1024 * 1024),
        pmc.PagefileUsage / (1024 * 1024),
      ))
    } else {
      None
    }
  }
}

/// Returns `(avail_phys_mb, avail_page_mb, avail_virt_mb)` from the
/// system.
///
/// - `avail_phys_mb` — free physical RAM. Low = system memory pressure.
/// - `avail_page_mb` — available commit charge (page file + physical RAM
///   headroom). Low = allocations fail even with free physical RAM.
/// - `avail_virt_mb` — free virtual address space in this process. Low =
///   VA exhaustion; allocations fail regardless of physical or page file.
#[cfg(target_os = "windows")]
fn system_avail_mb() -> Option<(u64, u64, u64)> {
  // SAFETY: `MEMORYSTATUSEX` is a plain C struct; `dwLength` must be set
  // to its size before calling `GlobalMemoryStatusEx`. The function fills
  // the struct on success (non-zero return).
  #[repr(C)]
  #[allow(non_snake_case, non_camel_case_types)]
  struct MEMORYSTATUSEX {
    dwLength: u32,
    dwMemoryLoad: u32,
    ullTotalPhys: u64,
    ullAvailPhys: u64,
    ullTotalPageFile: u64,
    ullAvailPageFile: u64,
    ullTotalVirtual: u64,
    ullAvailVirtual: u64,
    ullAvailExtendedVirtual: u64,
  }

  extern "system" {
    fn GlobalMemoryStatusEx(lpBuffer: *mut MEMORYSTATUSEX) -> i32;
  }

  unsafe {
    let mut mem_status = std::mem::zeroed::<MEMORYSTATUSEX>();
    mem_status.dwLength =
      u32::try_from(std::mem::size_of::<MEMORYSTATUSEX>())
        .unwrap_or_default();

    if GlobalMemoryStatusEx(&raw mut mem_status) != 0 {
      Some((
        mem_status.ullAvailPhys / (1024 * 1024),
        mem_status.ullAvailPageFile / (1024 * 1024),
        mem_status.ullAvailVirtual / (1024 * 1024),
      ))
    } else {
      None
    }
  }
}

/// Main entry point for the application.
///
/// Conditionally starts the WM or runs a CLI command based on the given
/// subcommand.
fn main() -> anyhow::Result<()> {
  install_panic_hook();

  let args = std::env::args().collect::<Vec<_>>();
  let app_command = AppCommand::parse_with_default(&args);

  if let AppCommand::Start {
    config_path,
    verbosity,
  } = app_command
  {
    let rt = tokio::runtime::Runtime::new()?;
    let (event_loop, dispatcher) = EventLoop::new()?;

    let task_handle = std::thread::spawn(move || {
      rt.block_on(async {
        let start_res =
          start_wm(config_path, verbosity, &dispatcher).await;

        if let Err(err) = &start_res {
          // If unable to start the WM, the error is fatal and a message
          // dialog is shown.
          tracing::error!("{:?}", err);
          dispatcher.show_error_dialog("Fatal error", &err.to_string());
        }

        if let Err(err) = dispatcher.stop_event_loop() {
          // Forcefully exit the process to ensure the event loop is
          // stopped.
          tracing::error!("Failed to stop event loop gracefully: {}", err);
          process::exit(1);
        }

        start_res
      })
    });

    // Run event loop (blocks until shutdown). This must be on the main
    // thread for macOS compatibility.
    event_loop.run()?;

    // Wait for clean exit of the WM.
    task_handle.join().unwrap()
  } else {
    let rt = tokio::runtime::Runtime::new()?;
    rt.block_on(wm_cli::start(args))
  }
}

#[allow(clippy::too_many_lines)]
async fn start_wm(
  config_path: Option<PathBuf>,
  verbosity: Verbosity,
  dispatcher: &Dispatcher,
) -> anyhow::Result<()> {
  setup_logging(&verbosity)?;

  // Ensure that only one instance of the WM is running.
  let _single_instance = SingleInstance::new()?;

  #[cfg(target_os = "macos")]
  {
    if !dispatcher.has_ax_permission(true) {
      anyhow::bail!(
        "Accessibility permissions are not granted. In System Preferences, \
         go to Privacy & Security > Accessibility and enable GlazeWM."
      );
    }
  }

  // Parse and validate user config.
  let mut config = UserConfig::new(config_path)?;

  // Add application icon to system tray.
  let mut tray = SystemTray::new(&config.path, dispatcher.clone())?;

  let mut wm = WindowManager::new(&mut config, dispatcher.clone())?;

  let mut ipc_server = IpcServer::start().await?;

  // On Windows, start watcher process for restoring hidden windows on
  // crash. macOS' hidden windows are always accessible.
  #[cfg(target_os = "windows")]
  if let Err(err) = start_watcher_process() {
    tracing::warn!(
      "Failed to start watcher process: {err}{}",
      cfg!(debug_assertions)
        .then_some(".\n Run `cargo build -p wm-watcher` to build it.")
        .unwrap_or_default()
    );
  }

  // On macOS, update the current process' PATH variable so that
  // `shell-exec` can resolve programs defined in the shell's PATH. Skip if
  // running via a terminal.
  #[cfg(target_os = "macos")]
  if !std::io::stdin().is_terminal() {
    update_path_env();
  }

  // Start listening for platform events after populating initial state.
  let mut window_listener = WindowListener::new(dispatcher)?;
  let mut display_listener = DisplayListener::new(dispatcher)?;
  let mut mouse_listener = MouseListener::new(
    if config.value.general.focus_follows_cursor {
      &[MouseEventKind::Move, MouseEventKind::LeftButtonUp]
    } else {
      &[MouseEventKind::LeftButtonUp]
    },
    dispatcher,
  )?;
  let mut keybinding_listener = KeybindingListener::new(
    &config
      .active_keybinding_configs(&[], false)
      .flat_map(|kb| kb.bindings)
      .collect::<Vec<_>>(),
    dispatcher,
  )?;

  // Run user's startup commands.
  if let Err(err) = wm.process_commands(
    &config.value.general.startup_commands.clone(),
    None,
    &mut config,
  ) {
    tracing::error!("{:?}", err);
    dispatcher.show_error_dialog("Non-fatal error", &err.to_string());
  }

  // Create an interval for periodically cleaning up invalid windows.
  let mut cleanup_interval = tokio::time::interval(Duration::from_secs(5));
  cleanup_interval
    .set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);

  loop {
    let res = tokio::select! {
      _ = signal::ctrl_c() => {
        tracing::info!("Received SIGINT signal.");
        break;
      },
      Some(()) = wm.exit_rx.recv() => {
        tracing::info!("Exiting through WM command.");
        break;
      },
      Some(()) = tray.exit_rx.recv() => {
        tracing::info!("Exiting through system tray.");
        break;
      },
      Some(event) = mouse_listener.next_event() => {
        tracing::debug!("Received mouse event: {:?}", event);
        wm.process_event(PlatformEvent::Mouse(event), &mut config)
      },
      Some(event) = window_listener.next_event() => {
        tracing::debug!("Received window event: {:?}", event);
        wm.process_event(PlatformEvent::Window(event), &mut config)
      },
      Some(()) = display_listener.next_event() => {
        tracing::debug!("Received display settings changed event.");
        wm.process_event(PlatformEvent::DisplaySettingsChanged, &mut config)
      },
      Some(event) = keybinding_listener.next_event() => {
        tracing::debug!("Received keyboard event: {:?}", event);
        wm.process_event(PlatformEvent::Keybinding(event), &mut config)
      }
      _ = cleanup_interval.tick() => {
        log_memory_diagnostics(&wm.state);

        // Re-register keyboard hook — Windows silently drops
        // WH_KEYBOARD_LL hooks after system events (sleep/wake,
        // lock screen, UAC, display changes, hook timeout).
        if let Err(err) = keybinding_listener.rehook() {
          tracing::warn!("Failed to re-register keyboard hook: {}", err);
        }

        // Wrap cleanup in `catch_unwind` to prevent a panic from
        // aborting the process — `process_event` is similarly protected.
        // Any panic is logged; the WM continues until the next tick.
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
          if wm.state.is_paused {
            Ok(())
          } else {
            wm.state.cleanup_invalid_windows()
          }
        }))
        .unwrap_or_else(|_| {
          tracing::error!("Panic in cleanup tick.");
          Ok(())
        })
      },
      Some((
        message,
        response_tx,
        disconnection_tx
      )) = ipc_server.message_rx.recv() => {
        tracing::info!("Received IPC message: {:?}", message);

        if let Err(err) = ipc_server.process_message(
          message,
          &response_tx,
          &disconnection_tx,
          &mut wm,
          &mut config,
        ) {
          tracing::error!("{:?}", err);
        }

        Ok(())
      },
      Some(wm_event) = wm.event_rx.recv() => {
        tracing::debug!("Received WM event: {:?}", wm_event);

        // Disable mouse listener when the WM is paused.
        if let WmEvent::PauseChanged { is_paused } = wm_event {
          let _ = mouse_listener.enable(!is_paused);
        }

        // Update keybinding and mouse listeners on config changes.
        if matches!(
          wm_event,
          WmEvent::UserConfigChanged { .. }
            | WmEvent::BindingModesChanged { .. }
            | WmEvent::PauseChanged { .. }
        ) {
          keybinding_listener.update(
            &config
              .active_keybinding_configs(&wm.state.binding_modes, false)
              .flat_map(|kb| kb.bindings)
              .collect::<Vec<_>>(),
          );

          mouse_listener.set_enabled_events(
            if config.value.general.focus_follows_cursor {
              &[MouseEventKind::Move, MouseEventKind::LeftButtonUp]
            } else {
              &[MouseEventKind::LeftButtonUp]
            },
          )?;
        }

        if let Err(err) = ipc_server.process_event(wm_event) {
          tracing::error!("{:?}", err);
        }

        Ok(())
      },
      Some(()) = tray.config_reload_rx.recv() => {
        wm.process_commands(
          &vec![InvokeCommand::WmReloadConfig],
          None,
          &mut config,
        ).map(|_| ())
      },
    };

    if let Err(err) = res {
      tracing::error!("{:?}", err);
    }
  }

  tracing::info!("Window manager shutting down.");
  wm.cleanup(&mut config, &mut ipc_server);

  Ok(())
}

/// Initialize logging with the specified verbosity level.
///
/// Error logs are saved to `~/.glzr/glazewm/errors.log`.
fn setup_logging(verbosity: &Verbosity) -> anyhow::Result<()> {
  let error_log_dir = home::home_dir()
    .context("Unable to get home directory.")?
    .join(".glzr/glazewm/");

  let error_writer =
    tracing_appender::rolling::never(&error_log_dir, "errors.log");

  // Write a startup marker directly to errors.log (bypassing the buffered
  // tracing writer) so we can confirm the binary ran and when.
  if let Ok(mut file) = std::fs::OpenOptions::new()
    .create(true)
    .append(true)
    .open(error_log_dir.join("errors.log"))
  {
    let now = std::time::SystemTime::now()
      .duration_since(std::time::UNIX_EPOCH)
      .map_or(0, |d| d.as_secs());
    let _ = writeln!(file, "START: glazewm started (unix={now})");
    let _ = file.flush();
  }

  let subscriber = tracing_subscriber::registry()
    .with(
      // Output to stdout with specified verbosity level.
      fmt::Layer::new()
        .with_writer(std::io::stdout.with_max_level(verbosity.level())),
    )
    .with(
      // Output to error log file.
      fmt::Layer::new()
        .with_writer(error_writer.with_max_level(Level::ERROR)),
    );

  tracing::subscriber::set_global_default(subscriber)?;

  tracing::info!(
    "Starting WM with log level {:?}.",
    verbosity.level().to_string()
  );

  Ok(())
}

/// Launches watcher binary (Windows-only). This is a separate process that
/// is responsible for restoring hidden windows in case the main WM process
/// crashes.
///
/// This assumes the watcher binary exists in the same directory as the
/// WM binary.
#[allow(unused)]
fn start_watcher_process() -> anyhow::Result<tokio::process::Child, Error>
{
  let watcher_path = env::current_exe()?
    .parent()
    .context("Failed to resolve path to the watcher process.")?
    .join("glazewm-watcher");

  Command::new(&watcher_path)
    .stdin(process::Stdio::null())
    .stdout(process::Stdio::null())
    .stderr(process::Stdio::null())
    .spawn()
    .context("Failed to start watcher process.")
}

/// Updates the current process' PATH by querying the login shell.
///
/// Apps launched outside a terminal (Spotlight, Finder, login items)
/// inherit a PATH that only contains `/usr/bin:/bin:/usr/sbin:/sbin`. This
/// causes `shell-exec` to fail for binaries that aren't in the system
/// PATH.
#[cfg(target_os = "macos")]
fn update_path_env() {
  let shell =
    std::env::var("SHELL").unwrap_or_else(|_| "/bin/zsh".to_string());

  // Use `-l` and `-i` (login + interactive) so that both profile and rc
  // files are sourced.
  let path_var = match std::process::Command::new(&shell)
    .args(["-lic", "printf '%s' \"$PATH\""])
    .output()
  {
    Ok(output) if output.status.success() => {
      String::from_utf8(output.stdout)
        .ok()
        .filter(|path| !path.is_empty())
    }
    _ => None,
  };

  if let Some(path) = path_var {
    std::env::set_var("PATH", path);
  } else {
    tracing::warn!(
      "Failed to query login shell for PATH. Keeping existing PATH."
    );
  }
}
