//! Sanitization of untrusted (candidate- or worker-provided) text.
//!
//! All such strings are stored and served as plain text (never HTML). We strip
//! control characters (keeping `\n` and `\t` only where multi-line text is
//! allowed), Unicode bidi overrides/isolates (Trojan-source style display
//! attacks) and zero-width/invisible formatting characters, then bound the
//! length on a character boundary.

const TRUNCATION_MARK: &str = "…[truncated]";

fn is_invisible_format(c: char) -> bool {
    matches!(
        c,
        '\u{200B}'..='\u{200F}'   // zero-width space/joiners, LRM/RLM
        | '\u{202A}'..='\u{202E}' // bidi embeddings/overrides
        | '\u{2060}'..='\u{2064}' // word joiner, invisible operators
        | '\u{2066}'..='\u{2069}' // bidi isolates
        | '\u{FEFF}'              // BOM / ZWNBSP
        | '\u{FFF9}'..='\u{FFFB}' // interlinear annotation
    )
}

fn clean(input: &str, multiline: bool, max_bytes: usize) -> String {
    let mut out = String::with_capacity(input.len().min(max_bytes.saturating_add(4)));
    for c in input.chars() {
        let c = match c {
            '\n' | '\t' if multiline => c,
            '\r' if multiline => continue,
            '\n' | '\t' | '\r' => ' ',
            c if c.is_control() || is_invisible_format(c) => continue,
            c => c,
        };
        out.push(c);
        if out.len() > max_bytes {
            break;
        }
    }
    if out.len() > max_bytes {
        let mut cut = max_bytes.saturating_sub(TRUNCATION_MARK.len());
        while !out.is_char_boundary(cut) {
            cut -= 1;
        }
        out.truncate(cut);
        if max_bytes >= TRUNCATION_MARK.len() {
            out.push_str(TRUNCATION_MARK);
        }
    }
    out
}

/// Multi-line plain text (logs, summaries). Keeps `\n` and `\t`.
pub fn sanitize_text(input: &str, max_bytes: usize) -> String {
    clean(input, true, max_bytes)
}

/// Single-line plain text (names, labels, reasons). Newlines/tabs become spaces.
pub fn sanitize_line(input: &str, max_bytes: usize) -> String {
    clean(input, false, max_bytes).trim().to_string()
}

/// Bounds used by the control plane.
pub const MAX_SUMMARY_BYTES: usize = 4096;
pub const MAX_LABEL_BYTES: usize = 256;
pub const MAX_NAME_BYTES: usize = 64;
pub const MAX_ERROR_BYTES: usize = 4096;
pub const MAX_REASON_BYTES: usize = 2048;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn strips_controls_and_bidi() {
        let s = "ok\u{0007}\u{202E}evil\u{200B}<b>\r\n\tx";
        assert_eq!(sanitize_text(s, 100), "okevil<b>\n\tx");
        assert_eq!(sanitize_line(s, 100), "okevil<b>   x");
    }
    #[test]
    fn bounds_length_on_char_boundary() {
        let s = "é".repeat(100);
        let out = sanitize_text(&s, 50);
        assert!(out.len() <= 50, "{}", out.len());
        assert!(out.ends_with(TRUNCATION_MARK));
        let short = sanitize_text("abc", 50);
        assert_eq!(short, "abc");
    }
}
