//! `npai-asm`: assemble NPAI v1 text into an image, or disassemble one.
//!
//! ```text
//! npai-asm <src.s> -o <out.npai>     assemble; prints the image SHA-256
//!                                    (the certificate's bytecodeDigest)
//! npai-asm --disasm <image.npai>     decode (exact NPAI v1 decoder) and print
//! npai-asm --digest <image.npai>     print SHA-256 and a Lean byte-list literal
//! ```
//! Syntax: see `arena_npai::asm` / runners/npai/README.md.
#![forbid(unsafe_code)]

use arena_npai::asm::{assemble_image, disassemble};
use arena_npai::interp::decode;
use arena_npai::report::to_hex;
use sha2::{Digest, Sha256};
use std::process::ExitCode;

const USAGE: &str =
    "usage: npai-asm <src> -o <out.npai> | npai-asm --disasm <image> | npai-asm --digest <image>";

fn die(msg: impl std::fmt::Display) -> ExitCode {
    eprintln!("npai-asm: {msg}");
    ExitCode::from(2)
}

fn lean_list(d: &[u8]) -> String {
    let xs: Vec<String> = d.iter().map(|b| format!("0x{b:02x}")).collect();
    format!("[{}]", xs.join(", "))
}

fn main() -> ExitCode {
    let a: Vec<String> = std::env::args().skip(1).collect();
    match a.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
        ["--disasm", f] => {
            let b = match std::fs::read(f) {
                Ok(b) => b,
                Err(e) => return die(format!("{f}: {e}")),
            };
            match decode(&b) {
                Some(p) => {
                    print!(
                        "; sha256 {}\n{}",
                        to_hex(&Sha256::digest(&b)),
                        disassemble(&p)
                    );
                    ExitCode::SUCCESS
                }
                None => die("decode error: not a valid NPAI v1 image"),
            }
        }
        ["--digest", f] => match std::fs::read(f) {
            Ok(b) => {
                let d = Sha256::digest(&b);
                println!("{}\n{}", to_hex(&d), lean_list(&d));
                ExitCode::SUCCESS
            }
            Err(e) => die(format!("{f}: {e}")),
        },
        [src, "-o", out] => {
            let text = match std::fs::read_to_string(src) {
                Ok(t) => t,
                Err(e) => return die(format!("{src}: {e}")),
            };
            let img = match assemble_image(&text) {
                Ok(i) => i,
                Err(e) => return die(format!("{src}: {e}")),
            };
            debug_assert!(decode(&img).is_some());
            if let Err(e) = std::fs::write(out, &img) {
                return die(format!("{out}: {e}"));
            }
            println!("{}", to_hex(&Sha256::digest(&img)));
            ExitCode::SUCCESS
        }
        _ => die(USAGE),
    }
}
