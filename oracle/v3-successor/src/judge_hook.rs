//! The shared judge (`oracle/v3/src/judge.rs`, unmodified, pinned by the signed D0 challenge's
//! generator specs) with an observation hook (workplan W01).
//!
//! Every item of the shared module is re-exported unchanged. `nearcore_judge` is the shared
//! function followed by an optional thread-local hook that sees the client and the witness bytes it
//! judged. No hook is installed unless a command installs one (`d12obs.rs`), so every other command
//! of this crate, including every generator, behaves exactly as with the shared module: the hook
//! never touches the client, the RNG or the verdict.

#[path = "../../v3/src/judge.rs"]
mod inner;
#[allow(unused_imports)]
pub use inner::*;

use near_client::Client;
use std::cell::RefCell;

pub type Hook = Box<dyn FnMut(&Client, &[u8], &[Vec<u8>])>;

thread_local! {
    static HOOK: RefCell<Option<Hook>> = const { RefCell::new(None) };
}

/// Install (or, with `None`, remove) this thread's hook.
pub fn set_hook(h: Option<Hook>) {
    HOOK.with(|x| *x.borrow_mut() = h);
}

/// `judge::nearcore_judge`, then the hook (if any) on the same inputs. The verdict is the shared
/// function's.
pub fn nearcore_judge(client: &Client, bytes: &[u8], codes: &[Vec<u8>], rs: (u16, u16)) -> Result<(), String> {
    let r = inner::nearcore_judge(client, bytes, codes, rs);
    HOOK.with(|x| {
        if let Some(f) = x.borrow_mut().as_mut() {
            f(client, bytes, codes);
        }
    });
    r
}
