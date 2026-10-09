import NearSpecV3.ChallengeD0a

/-!
`nearspec-v3-check-d0a CASE_DIR...` — the compiled amended relation `NearSpecV3.checkD0a`
(`.ok ()` ⇔ `RelD0a`, `relD0a_iff`) on `claim.bin` / `witness.bin` of each case directory;
one JSON line per case: `{"case", "verdict": "accept" | "reject" | "out_of_domain", "reason"}`.
Plain spec code (no candidate fast paths), so it is the reference side of the difftest.
-/

open NearSpecV3

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

/-- Usage: `nearspec-v3-check-d0a [--bound B] [--words-bound W] [--depth-bound D] CASE_DIR...`
(defaults `B0`, `W0`, `Dp0`). Each line also reports `unfold` = `unfoldBytes` (A7),
`chacha_words` = `chachaWords` (A9) and `max_path_depth` = `maxPathDepth` (A10). -/
def parseFlags (B W D : Nat) : List String → Nat × Nat × Nat × List String
  | "--bound" :: b :: rest => parseFlags b.toNat! W D rest
  | "--words-bound" :: b :: rest => parseFlags B b.toNat! D rest
  | "--depth-bound" :: b :: rest => parseFlags B W b.toNat! rest
  | rest => (B, W, D, rest)

def main (args : List String) : IO UInt32 := do
  let (B, W, D, args) := parseFlags B0 W0 Dp0 args
  for dir in args do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let u := unfoldBytes cb.toList wb.toList
    let k := chachaWords cb.toList wb.toList
    let p := maxPathDepth cb.toList wb.toList
    let (v, reason) := match checkD0a B cb.toList wb.toList W D with
      | .ok () => ("accept", "")
      | .error e => (if e.startsWith "out of domain" then "out_of_domain" else "reject", e)
    IO.println s!"\{\"case\": \"{esc dir}\", \"verdict\": \"{v}\", \"reason\": \"{esc reason}\", \"unfold\": {u}, \"chacha_words\": {k}, \"max_path_depth\": {p}}"
  return 0
