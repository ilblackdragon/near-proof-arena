//! STUB — the `rcpt` table (`ZkFormal/Near/Render/Rcpt.lean`) is ported by
//! another sub-agent (lane/zk-L8c-rcpt), which replaces this file.

use super::info::{Info, Msg};

/// `rcptRowsAll I` (stub: empty).
pub fn rcpt_rows_all(_i: &Info) -> Vec<Vec<u32>> { vec![] }

/// `rcptMsgs I` (stub: empty; see `sim::rcpt_msgs_sim` for the RcptSim port).
pub fn rcpt_msgs(_i: &Info) -> Vec<Msg> { vec![] }
