//! Sound detection of sandbox-escape attempts.
//!
//! A sandbox init (Firecracker guest `arena-init`, bwrap-dev helper init)
//! installs a seccomp filter on the candidate process *just before exec*.
//! Syscalls that no legitimate candidate needs (kernel attack surface,
//! namespace/mount games, tracing other processes, raw/IP/netlink sockets)
//! return `SECCOMP_RET_USER_NOTIF`: the kernel blocks the calling thread and
//! hands the event to the init over a listener fd that only the init holds.
//! The init records the event and answers `-EPERM`, so the attempt is both
//! **contained** (the syscall never runs) and **reported**.
//!
//! Soundness (no false positives): a violation is recorded only when the
//! kernel delivered a notification, i.e. a task under the filter actually
//! executed one of the listed syscalls (with the listed arguments). Filters
//! are inherited across fork/clone and kept across execve and cannot be
//! removed, so every process the candidate starts is covered. The listener
//! is created inside the child after it dropped privileges and is passed to
//! the init over a close-on-exec socketpair, then closed: the candidate never
//! holds it. Completeness caveat: an attempt whose task is killed before the
//! init reads the notification (the kernel withdraws it) is still blocked
//! but may not be counted.
//!
//! Usage (all three steps are required):
//! ```ignore
//! let prep = Prepared::new(Policy::Strict)?;       // before fork
//! cmd.pre_exec(move || prep_child.install());       // child, after setuid/NNP
//! let mon = prep.start_monitor()?;                  // parent, after spawn
//! ... wait for the whole tree ...
//! let violations = mon.finish();
//! ```

use serde::{Deserialize, Serialize};
use std::io;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

/// Which syscalls count as sandbox violations.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Policy {
    /// No filter (no detection).
    #[default]
    Off,
    /// Candidate entry points (`prepare`/`prove`/`verify`): kernel attack
    /// surface + IP/raw/netlink sockets.
    Strict,
    /// Build recipes and judge tooling (Lean, compilers): kernel attack
    /// surface only; network attempts just fail (there is no network) and
    /// are judged by their effect (e.g. BUILD_FAILED).
    Tooling,
}

/// One kind of violation with its count.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Violation {
    /// e.g. `ptrace`, `socket(AF_INET)`, `non-native-abi`.
    pub what: String,
    pub count: u64,
    /// pid (in the sandbox's pid namespace) of the first offender.
    pub first_pid: u32,
}

pub fn describe(v: &[Violation]) -> String {
    v.iter()
        .map(|x| format!("{} x{}", x.what, x.count))
        .collect::<Vec<_>>()
        .join(", ")
}

// x86_64 syscall numbers that are violations under every policy.
const KERNEL_ATTACK: &[(u32, &str)] = &[
    (101, "ptrace"),
    (310, "process_vm_readv"),
    (311, "process_vm_writev"),
    (438, "pidfd_getfd"),
    (165, "mount"),
    (166, "umount2"),
    (155, "pivot_root"),
    (161, "chroot"),
    (272, "unshare"),
    (308, "setns"),
    (428, "open_tree"),
    (429, "move_mount"),
    (430, "fsopen"),
    (431, "fsconfig"),
    (432, "fsmount"),
    (433, "fspick"),
    (442, "mount_setattr"),
    (304, "open_by_handle_at"),
    (167, "swapon"),
    (168, "swapoff"),
    (169, "reboot"),
    (170, "sethostname"),
    (171, "setdomainname"),
    (172, "iopl"),
    (173, "ioperm"),
    (174, "create_module"),
    (175, "init_module"),
    (176, "delete_module"),
    (313, "finit_module"),
    (246, "kexec_load"),
    (320, "kexec_file_load"),
    (163, "acct"),
    (164, "settimeofday"),
    (227, "clock_settime"),
    (179, "quotactl"),
    (180, "nfsservctl"),
    (103, "syslog"),
    (298, "perf_event_open"),
    (321, "bpf"),
    (248, "add_key"),
    (249, "request_key"),
    (250, "keyctl"),
    (300, "fanotify_init"),
    (212, "lookup_dcookie"),
    (134, "uselib"),
    (153, "vhangup"),
];
const SYS_SOCKET: u32 = 41;
/// Socket families that are violations under `Strict`.
const BAD_FAMILIES: &[(u32, &str)] = &[
    (2, "AF_INET"),
    (10, "AF_INET6"),
    (16, "AF_NETLINK"),
    (17, "AF_PACKET"),
];
const AUDIT_ARCH_X86_64: u32 = 0xc000_003e;
const X32_BIT: u32 = 0x4000_0000;

fn stmt(code: u16, k: u32) -> libc::sock_filter {
    libc::sock_filter {
        code,
        jt: 0,
        jf: 0,
        k,
    }
}
fn jeq(k: u32, jt: u8) -> libc::sock_filter {
    libc::sock_filter {
        code: 0x15,
        jt,
        jf: 0,
        k,
    } // BPF_JMP|BPF_JEQ|BPF_K
}
const LD_W_ABS: u16 = 0x20;
const RET_K: u16 = 0x06;

/// Builds the BPF program for `policy` (x86_64).
pub fn program(policy: Policy) -> Vec<libc::sock_filter> {
    assert!(policy != Policy::Off);
    // Layout: [header][nr checks][socket jump][ALLOW][socket block][NOTIFY]
    let nr = KERNEL_ATTACK.len();
    let strict = policy == Policy::Strict;
    let sock_block = if strict {
        1 + BAD_FAMILIES.len() + 1
    } else {
        0
    };
    // indices
    let header = 4; // ld arch; jeq x86_64; ld nr; jset x32
    let checks_start = header;
    let sock_jump = checks_start + nr; // present only if strict
    let allow = sock_jump + usize::from(strict);
    let sock_start = allow + 1;
    let notify = sock_start + sock_block;
    let rel = |from: usize, to: usize| -> u8 { u8::try_from(to - from - 1).expect("jump fits") };
    let mut p = Vec::with_capacity(notify + 1);
    p.push(stmt(LD_W_ABS, 4)); // 0: arch
    p.push(libc::sock_filter {
        code: 0x15,
        jt: 0,
        jf: rel(1, notify),
        k: AUDIT_ARCH_X86_64,
    }); // 1
    p.push(stmt(LD_W_ABS, 0)); // 2: nr
    p.push(libc::sock_filter {
        code: 0x45,
        jt: rel(3, notify),
        jf: 0,
        k: X32_BIT,
    }); // 3: JSET
    for (i, (n, _)) in KERNEL_ATTACK.iter().enumerate() {
        p.push(jeq(*n, rel(checks_start + i, notify)));
    }
    if strict {
        p.push(jeq(SYS_SOCKET, rel(sock_jump, sock_start)));
    }
    p.push(stmt(RET_K, libc::SECCOMP_RET_ALLOW)); // allow
    if strict {
        p.push(stmt(LD_W_ABS, 16)); // args[0] low 32 bits
        for (i, (f, _)) in BAD_FAMILIES.iter().enumerate() {
            p.push(jeq(*f, rel(sock_start + 1 + i, notify)));
        }
        p.push(stmt(RET_K, libc::SECCOMP_RET_ALLOW));
    }
    p.push(stmt(RET_K, libc::SECCOMP_RET_USER_NOTIF)); // notify
    assert_eq!(p.len(), notify + 1);
    p
}

fn classify(data: &libc::seccomp_data) -> String {
    if data.arch != AUDIT_ARCH_X86_64 {
        return format!("non-native-abi(arch={:#x},nr={})", data.arch, data.nr);
    }
    let nr = data.nr as u32;
    if nr & X32_BIT != 0 {
        return format!("x32-abi(nr={})", nr & !X32_BIT);
    }
    if nr == SYS_SOCKET {
        let fam = data.args[0] as u32;
        let name = BAD_FAMILIES
            .iter()
            .find(|(f, _)| *f == fam)
            .map(|(_, n)| *n)
            .unwrap_or("?");
        return format!("socket({name})");
    }
    KERNEL_ATTACK
        .iter()
        .find(|(n, _)| *n == nr)
        .map(|(_, s)| s.to_string())
        .unwrap_or_else(|| format!("syscall {nr}"))
}

/// Filter + socketpair, created before fork.
pub struct Prepared {
    prog: Arc<Vec<libc::sock_filter>>,
    parent: OwnedFd,
    child: OwnedFd,
}

/// What the child closure needs (all plain data; async-signal-safe use).
#[derive(Clone)]
pub struct ChildSide {
    prog: Arc<Vec<libc::sock_filter>>,
    child_fd: RawFd,
    parent_fd: RawFd,
}

impl Prepared {
    pub fn new(policy: Policy) -> io::Result<Option<Prepared>> {
        if policy == Policy::Off {
            return Ok(None);
        }
        let mut fds = [0 as libc::c_int; 2];
        let r = unsafe {
            libc::socketpair(
                libc::AF_UNIX,
                libc::SOCK_SEQPACKET | libc::SOCK_CLOEXEC,
                0,
                fds.as_mut_ptr(),
            )
        };
        if r != 0 {
            return Err(io::Error::last_os_error());
        }
        let (parent, child) =
            unsafe { (OwnedFd::from_raw_fd(fds[0]), OwnedFd::from_raw_fd(fds[1])) };
        Ok(Some(Prepared {
            prog: Arc::new(program(policy)),
            parent,
            child,
        }))
    }

    pub fn child_side(&self) -> ChildSide {
        ChildSide {
            prog: self.prog.clone(),
            child_fd: self.child.as_raw_fd(),
            parent_fd: self.parent.as_raw_fd(),
        }
    }

    /// Parent, after the child exec'd (or failed to): receive the listener
    /// and start answering notifications. If the child never installed the
    /// filter (exec failure before install), returns an idle monitor.
    pub fn start_monitor(self) -> io::Result<Monitor> {
        drop(self.child);
        let listener = recv_fd(self.parent.as_raw_fd())?;
        let found = Arc::new(Mutex::new(Vec::<Violation>::new()));
        let stop = Arc::new(AtomicBool::new(false));
        let thread = listener.map(|l| {
            let (found, stop) = (found.clone(), stop.clone());
            std::thread::spawn(move || serve(l, found, stop))
        });
        Ok(Monitor {
            found,
            stop,
            thread,
        })
    }
}

impl ChildSide {
    /// In the child (`pre_exec`), as the LAST step before exec: requires
    /// `PR_SET_NO_NEW_PRIVS` (or CAP_SYS_ADMIN). Async-signal-safe.
    pub fn install(&self) -> io::Result<()> {
        unsafe {
            libc::close(self.parent_fd);
            let fprog = libc::sock_fprog {
                len: self.prog.len() as u16,
                filter: self.prog.as_ptr() as *mut _,
            };
            let l = libc::syscall(
                libc::SYS_seccomp,
                libc::SECCOMP_SET_MODE_FILTER,
                libc::SECCOMP_FILTER_FLAG_NEW_LISTENER,
                &fprog as *const libc::sock_fprog,
            );
            if l < 0 {
                return Err(io::Error::last_os_error());
            }
            let l = l as libc::c_int;
            let r = send_fd(self.child_fd, l);
            libc::close(l);
            libc::close(self.child_fd);
            r
        }
    }
}

/// Collects violations until [`Monitor::finish`].
pub struct Monitor {
    found: Arc<Mutex<Vec<Violation>>>,
    stop: Arc<AtomicBool>,
    thread: Option<std::thread::JoinHandle<()>>,
}

impl Monitor {
    /// Call after every process of the tree is gone.
    pub fn finish(mut self) -> Vec<Violation> {
        self.stop.store(true, Ordering::SeqCst);
        if let Some(t) = self.thread.take() {
            let _ = t.join();
        }
        let v = self.found.lock().unwrap().clone();
        v
    }
}

unsafe fn send_fd(sock: RawFd, fd: RawFd) -> io::Result<()> {
    let mut byte = [0u8; 1];
    let mut iov = libc::iovec {
        iov_base: byte.as_mut_ptr() as *mut _,
        iov_len: 1,
    };
    let mut cbuf = [0u64; 4]; // CMSG_SPACE(sizeof(int)) = 24 bytes, aligned
    let mut msg: libc::msghdr = std::mem::zeroed();
    msg.msg_iov = &mut iov;
    msg.msg_iovlen = 1;
    msg.msg_control = cbuf.as_mut_ptr() as *mut _;
    msg.msg_controllen = libc::CMSG_SPACE(std::mem::size_of::<libc::c_int>() as u32) as _;
    let c = libc::CMSG_FIRSTHDR(&msg);
    (*c).cmsg_level = libc::SOL_SOCKET;
    (*c).cmsg_type = libc::SCM_RIGHTS;
    (*c).cmsg_len = libc::CMSG_LEN(std::mem::size_of::<libc::c_int>() as u32) as _;
    std::ptr::write_unaligned(libc::CMSG_DATA(c) as *mut libc::c_int, fd);
    if libc::sendmsg(sock, &msg, libc::MSG_NOSIGNAL) != 1 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

/// `Ok(None)` if the peer closed without sending (filter never installed).
fn recv_fd(sock: RawFd) -> io::Result<Option<OwnedFd>> {
    unsafe {
        let mut byte = [0u8; 1];
        let mut iov = libc::iovec {
            iov_base: byte.as_mut_ptr() as *mut _,
            iov_len: 1,
        };
        let mut cbuf = [0u64; 4];
        let mut msg: libc::msghdr = std::mem::zeroed();
        msg.msg_iov = &mut iov;
        msg.msg_iovlen = 1;
        msg.msg_control = cbuf.as_mut_ptr() as *mut _;
        msg.msg_controllen = std::mem::size_of_val(&cbuf) as _;
        loop {
            let n = libc::recvmsg(sock, &mut msg, libc::MSG_CMSG_CLOEXEC);
            if n < 0 {
                let e = io::Error::last_os_error();
                if e.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(e);
            }
            if n == 0 {
                return Ok(None);
            }
            break;
        }
        let c = libc::CMSG_FIRSTHDR(&msg);
        if c.is_null() || (*c).cmsg_level != libc::SOL_SOCKET || (*c).cmsg_type != libc::SCM_RIGHTS
        {
            return Err(io::Error::other("seccomp listener not received"));
        }
        let fd = std::ptr::read_unaligned(libc::CMSG_DATA(c) as *const libc::c_int);
        Ok(Some(OwnedFd::from_raw_fd(fd)))
    }
}

fn serve(listener: OwnedFd, found: Arc<Mutex<Vec<Violation>>>, stop: Arc<AtomicBool>) {
    let fd = listener.as_raw_fd();
    loop {
        let mut pfd = libc::pollfd {
            fd,
            events: libc::POLLIN,
            revents: 0,
        };
        let r = unsafe { libc::poll(&mut pfd, 1, 50) };
        if r < 0 {
            if io::Error::last_os_error().kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return;
        }
        if r == 0 {
            if stop.load(Ordering::SeqCst) {
                return;
            }
            continue;
        }
        if pfd.revents & libc::POLLIN == 0 {
            // POLLHUP: no task uses the filter any more
            if stop.load(Ordering::SeqCst) || pfd.revents & (libc::POLLHUP | libc::POLLERR) != 0 {
                return;
            }
            continue;
        }
        let mut req: libc::seccomp_notif = unsafe { std::mem::zeroed() };
        if unsafe { libc::ioctl(fd, libc::SECCOMP_IOCTL_NOTIF_RECV as _, &mut req) } != 0 {
            continue; // ENOENT: the task died before we read it
        }
        let what = classify(&req.data);
        {
            let mut f = found.lock().unwrap();
            if let Some(v) = f.iter_mut().find(|v| v.what == what) {
                v.count += 1;
            } else if f.len() < 64 {
                f.push(Violation {
                    what,
                    count: 1,
                    first_pid: req.pid,
                });
            }
        }
        let mut resp = libc::seccomp_notif_resp {
            id: req.id,
            val: 0,
            error: -libc::EPERM,
            flags: 0,
        };
        unsafe { libc::ioctl(fd, libc::SECCOMP_IOCTL_NOTIF_SEND as _, &mut resp) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::process::CommandExt;
    use std::process::Command;

    fn run(policy: Policy, script: &str) -> (std::process::ExitStatus, Vec<Violation>) {
        let prep = Prepared::new(policy).unwrap().unwrap();
        let cs = prep.child_side();
        let mut cmd = Command::new("/bin/sh");
        cmd.args(["-c", script]);
        unsafe {
            cmd.pre_exec(move || {
                if libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0 {
                    return Err(io::Error::last_os_error());
                }
                cs.install()
            });
        }
        let mut child = cmd.spawn().unwrap();
        let mon = prep.start_monitor().unwrap();
        let st = child.wait().unwrap();
        (st, mon.finish())
    }

    #[test]
    fn program_shape() {
        for p in [Policy::Strict, Policy::Tooling] {
            let prog = program(p);
            assert!(prog.len() < 128);
        }
    }

    #[test]
    fn honest_commands_are_clean() {
        let (st, v) = run(
            Policy::Strict,
            "echo hi > /dev/null; ls / > /dev/null; cat /proc/self/status > /dev/null; sh -c true",
        );
        assert!(st.success());
        assert!(v.is_empty(), "{v:?}");
    }

    #[test]
    fn strict_flags_ip_sockets_only() {
        let (st, v) = run(
            Policy::Strict,
            "perl -MSocket -e 'socket(my $u, PF_UNIX, SOCK_STREAM, 0) or exit 4; socket(my $s, PF_INET, SOCK_STREAM, 0) and exit 3; exit 0'",
        );
        assert!(st.success(), "{st:?}");
        assert_eq!(v.len(), 1, "{v:?}");
        assert_eq!(v[0].what, "socket(AF_INET)");
        let (_, v) = run(
            Policy::Tooling,
            "perl -MSocket -e 'socket(my $s, PF_INET, SOCK_STREAM, 0)'",
        );
        assert!(v.is_empty(), "tooling ignores sockets: {v:?}");
    }

    #[test]
    fn violations_are_reported_and_denied() {
        // unshare(1) needs unshare(2); it must fail with EPERM and be reported
        let (st, v) = run(Policy::Tooling, "unshare -U true 2>/dev/null; echo rc=$?");
        assert!(st.success());
        assert!(v.iter().any(|x| x.what == "unshare"), "{v:?}");
    }
}
