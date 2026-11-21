import WasmBase.HostCtx
import WasmBase.Main.RegMemLink
import WasmBase.Main.HostFoot

/-!
# WasmBase.Main.HostAns — explicit answer functions of corpus host functions (E2E M6, HOSTIF)

For the simplest host functions the corpus calls (`m6/host-freq.md`: `register_len` 6, `input` 48,
`read_register` 49), an explicit **answer function** `ans… σ args (memSz)` returning an `HAns`: the
error (or `none`), the pushed `i64` result words, the gas record after the call, the register file
and register usage after it, and the memory writes `(ptr, bytes)`.  It reads only host-side fields
of `σ` (`gas`, `registers`, `regUsage`, `ctx`) plus, for `read_register`, the memory size.

`postOf s a` is the state the arm ends in from the post-pop state `s` (writes applied, results pushed,
`a`'s gas/registers/usage); `runOf s a` the `EStateM` result (`.ok`/`.error` with that state).
Proved — every branch, every error:

* **`register_len_ans`**: `(hostCall "register_len").get!.run s = runOf s' (ansRegisterLen s' (topArg s))`,
  `s' = { s with stack := s.stack.pop }`;
* **`input_ans`**: the same for `input` / `ansInput`;
* **`read_register_ans`**: from `(popArgs 2).run s = .ok args s0`,
  `(hostCall "read_register").get!.run s = runOf s0 (ansReadRegister s0 args[0] args[1] (memBytes s0))`.

Method note (kernel/elaborator cost): every charge result is a *parameter* (`…G` forms with equations
`payBase … = p`), never generalised out of the goal: `payBase` terms nested in one another make
`rcases`/`rw` key-matching unfold them and diverge.  The generic two-run footprint is FOOT2's; these
are its explicit instances, and the producer's target (`Main/HostIfTape.lean`, `ProducerObl`).
-/

namespace WasmBase
namespace HostAns

open NearSpecV3.Wasm
set_option linter.deprecated false

structure HAns where
  err : Option String
  res : List Nat
  gas : Gas
  regs : Array (Nat × ByteArray)
  regUsage : Nat
  wr : List (Nat × ByteArray)

def postOf (s : St) (a : HAns) : St :=
  a.res.foldl (fun t v => pushI64 t v)
    { a.wr.foldl (fun t w => writeBytes t w.1 w.2) s with gas := a.gas, registers := a.regs, regUsage := a.regUsage }

def runOf (s : St) (a : HAns) : EStateM.Result String St Unit :=
  match a.err with
  | none => .ok () (postOf s a)
  | some e => .error e (postOf s a)

def regLen (σ : St) (id : Nat) : Nat := ((σ.registers.find? (·.1 = id)).map (·.2.size)).getD (u64Bound - 1)

def ansRegisterLen (σ : St) (id : Nat) : HAns :=
  ⟨(payBase σ.gas C.base).2, if (payBase σ.gas C.base).2.isNone then [regLen σ id] else [],
    (payBase σ.gas C.base).1, σ.registers, σ.regUsage, []⟩

theorem register_len_tail (t : St) (id : Nat) :
    (((payBaseH C.base) >>= fun _ => (get : HM St) >>= fun x =>
      pushRet ((Option.map (fun x => x.snd.size) (Array.find? (fun x => decide (x.fst = id)) x.registers)).getD
        (u64Bound - 1))) : HM Unit).run t = runOf t (ansRegisterLen t id) := by
  unfold ansRegisterLen
  have hp := payBaseH_run C.base t
  rcases hq : payBase t.gas C.base with ⟨g, _ | e⟩
  · have e1 : (payBaseH C.base).run t = .ok () { t with gas := g } := by
      rw [hp]; split
      · next e' h => rw [hq] at h; cases h
      · next h => rw [hq]
    rw [bind_ok e1, bind_ok (hmGet_run _), pushRet_run]
    rfl
  · have e1 : (payBaseH C.base).run t = .error e { t with gas := g } := by
      rw [hp]; split
      · next e' h => rw [hq] at h ⊢; cases h; rfl
      · next h => rw [hq] at h; cases h
    rw [bind_err e1]
    rfl

theorem register_len_ans (s : St) :
    (hostCall "register_len").get!.run s =
      runOf { s with stack := s.stack.pop } (ansRegisterLen { s with stack := s.stack.pop } (topArg s)) := by
  rw [hostCall.eq_2]; simp only [Option.get!]
  rw [bind_run, popArgs1_run]
  exact register_len_tail _ _

/-- The register-file update of `regSetH` (its `regs`). -/
def regSetRegsOf (R : Array (Nat × ByteArray)) (id : Nat) (d : ByteArray) : Array (Nat × ByteArray) :=
  match R.findIdx? (·.1 = id) with
  | some i => R.set! i (id, d)
  | none => R.push (id, d)

/-- The register usage after `regSetH`. -/
def regUsageOf (σ : St) (id : Nat) (d : ByteArray) : Nat :=
  σ.regUsage - (match σ.registers.find? (·.1 = id) with
    | some (_, o) => o.size + 8
    | none => 0) + (d.size + 8)

def mavErr : String := s!"HostError({"MemoryAccessViolation"})"

/-- `regSetH`'s checks after its charges (gas `g` already paid). -/
def regSetAns (σ : St) (g : Gas) (id : Nat) (d : ByteArray) : HAns :=
  if d.size > maxRegisterSize then ⟨some mavErr, [], g, σ.registers, σ.regUsage, []⟩
  else if σ.registers.size ≥ maxNumberRegisters then ⟨some mavErr, [], g, σ.registers, σ.regUsage, []⟩
  else if regUsageOf σ id d > registersMemoryLimit then ⟨some mavErr, [], g, σ.registers, σ.regUsage, []⟩
  else ⟨none, [], g, regSetRegsOf σ.registers id d, regUsageOf σ id d, []⟩

/-- **`input`** (hid 48): base charge, the register-write base charge (no per-byte charge), then
`regSetH id ctx.input`. -/
def ansInputG (σ : St) (p1 p2 : Gas × Option String) (id : Nat) : HAns :=
  if p1.2.isSome then ⟨p1.2, [], p1.1, σ.registers, σ.regUsage, []⟩
  else if p2.2.isSome then ⟨p2.2, [], p2.1, σ.registers, σ.regUsage, []⟩
  else regSetAns σ p2.1 id σ.ctx.input

def ansInput (σ : St) (id : Nat) : HAns :=
  ansInputG σ (payBase σ.gas C.base) (payBase (payBase σ.gas C.base).1 C.writeRegisterBase) id

/-- `payBaseH` without the dependent match. -/
theorem payBaseH_ok' {c : Cost} {t : St} {g : Gas} (hq : payBase t.gas c = (g, none)) :
    (payBaseH c).run t = .ok () { t with gas := g } := by
  have hp := payBaseH_run c t
  rw [hp]; split
  · next e' h => rw [hq] at h; cases h
  · next h => rw [hq]

theorem payBaseH_err' {c : Cost} {t : St} {g : Gas} {e : String} (hq : payBase t.gas c = (g, some e)) :
    (payBaseH c).run t = .error e { t with gas := g } := by
  have hp := payBaseH_run c t
  rw [hp]; split
  · next e' h => rw [hq] at h ⊢; cases h; rfl
  · next h => rw [hq] at h; cases h

/-- `regSetH id d false` after its base charge: `regSetAns`. -/
theorem regSetH_nob (t : St) (id : Nat) (d : ByteArray) :
    (regSetH id d false).run t =
      runOf t (if (payBase t.gas C.writeRegisterBase).2.isSome then
        ⟨(payBase t.gas C.writeRegisterBase).2, [], (payBase t.gas C.writeRegisterBase).1, t.registers, t.regUsage, []⟩
        else regSetAns t (payBase t.gas C.writeRegisterBase).1 id d) := by
  unfold regSetH
  rcases hq : payBase t.gas C.writeRegisterBase with ⟨g, _ | e⟩
  · rw [bind_ok (payBaseH_ok' hq)]
    simp only [Option.isSome, Bool.false_eq_true, ite_false]
    rw [bind_ok (hmGet_run _)]
    unfold regSetAns
    dsimp only
    by_cases h1 : d.size > maxRegisterSize
    · rw [if_pos h1, if_pos h1]; rfl
    rw [if_neg h1, if_neg h1]
    by_cases h2 : t.registers.size ≥ maxNumberRegisters
    · rw [if_pos h2, if_pos h2]; rfl
    rw [if_neg h2, if_neg h2]
    by_cases h4 : regUsageOf t id d > registersMemoryLimit
    · rw [if_pos h4]
      split
      · rfl
      · next h3 => exact absurd h4 h3
    · rw [if_neg h4]
      split
      · next h3 => exact absurd h3 h4
      · rfl
  · rw [bind_err (payBaseH_err' hq)]
    rfl

theorem regSetAns_gas (t : St) (g g' : Gas) (id : Nat) (d : ByteArray) :
    regSetAns { t with gas := g' } g id d = regSetAns t g id d := rfl

theorem postOf_gas (t : St) (g : Gas) (a : HAns) (hw : a.wr = []) :
    postOf { t with gas := g } a = postOf t a := by
  unfold postOf; rw [hw]; rfl

theorem runOf_gas (t : St) (g : Gas) (a : HAns) (hw : a.wr = []) :
    runOf { t with gas := g } a = runOf t a := by
  unfold runOf; rw [postOf_gas t g a hw]

theorem regSetAns_wr (t : St) (g : Gas) (id : Nat) (d : ByteArray) : (regSetAns t g id d).wr = [] := by
  unfold regSetAns; split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem input_tailG (t : St) (id : Nat) (p1 p2 : Gas × Option String)
    (h1 : payBase t.gas C.base = p1) (h2 : payBase p1.1 C.writeRegisterBase = p2) :
    (((payBaseH C.base) >>= fun _ => (get : HM St) >>= fun x => regSetH id x.ctx.input false) : HM Unit).run t =
      runOf t (ansInputG t p1 p2 id) := by
  rcases p1 with ⟨g, _ | e⟩
  · rw [bind_ok (payBaseH_ok' h1), bind_ok (hmGet_run _), regSetH_nob]
    dsimp only at h2 ⊢
    rw [h2]
    rcases p2 with ⟨g2, _ | e2⟩
    · unfold ansInputG
      simp only [Option.isSome, Bool.false_eq_true, ite_false]
      rw [regSetAns_gas, runOf_gas _ _ _ (regSetAns_wr _ _ _ _)]
    · unfold ansInputG
      simp only [Option.isSome, Bool.false_eq_true, ite_false, ite_true]
      rw [runOf_gas _ _ _ rfl]
  · rw [bind_err (payBaseH_err' h1)]
    unfold ansInputG
    simp only [Option.isSome, ite_true]
    rfl

/-- **`input`'s arm is its answer function**, every branch. -/
theorem input_ans (s : St) :
    (hostCall "input").get!.run s =
      runOf { s with stack := s.stack.pop } (ansInput { s with stack := s.stack.pop } (topArg s)) := by
  rw [hostCall.eq_10]; simp only [Option.get!]
  rw [bind_run, popArgs1_run]
  exact input_tailG _ _ _ _ rfl rfl


/-! ## `read_register` (hid 49, `(2, 0)`) -/

theorem payPerH_ok' {c : Cost} {n : Nat} {t : St} {g : Gas} (hq : payPer t.gas c n = (g, none)) :
    (payPerH c n).run t = .ok () { t with gas := g } := by
  have hp := withGas_run (payPer · c n) t
  rewrite [payPerH, hp]; split
  · next e' h => simp only [hq] at h; cases h
  · next h => simp only [hq]

theorem payPerH_err' {c : Cost} {n : Nat} {t : St} {g : Gas} {e : String} (hq : payPer t.gas c n = (g, some e)) :
    (payPerH c n).run t = .error e { t with gas := g } := by
  have hp := withGas_run (payPer · c n) t
  rewrite [payPerH, hp]; split
  · next e' h => simp only [hq] at h ⊢; cases h; rfl
  · next h => simp only [hq] at h; cases h

/-- The error of a missing register. -/
def invErr (id : Nat) : String := s!"HostError({s!"InvalidRegisterId \{ register_id: {id} }"})"

/-- An error answer with gas `g`. -/
def errA (σ : St) (e : Option String) (g : Gas) : HAns := ⟨e, [], g, σ.registers, σ.regUsage, []⟩

/-- **`read_register`** with its five charges' results as parameters: base charge `p1`, then the
register (`dr`) is read (`InvalidRegisterId` if absent) with charges `pr1`, `pr2`, then written to
memory at `ptr` with charges `pw1`, `pw2` and the bounds check against `memSz`. -/
def ansReadRegisterG (σ : St) (id ptr memSz : Nat) (dr : Option ByteArray)
    (p1 pr1 pr2 pw1 pw2 : Gas × Option String) : HAns :=
  if p1.2.isSome then errA σ p1.2 p1.1 else
  match dr with
  | none => errA σ (some (invErr id)) p1.1
  | some d =>
    if pr1.2.isSome then errA σ pr1.2 pr1.1
    else if pr2.2.isSome then errA σ pr2.2 pr2.1
    else if pw1.2.isSome then errA σ pw1.2 pw1.1
    else if pw2.2.isSome then errA σ pw2.2 pw2.1
    else if ptr + d.size > memSz then errA σ (some mavErr) pw2.1
    else ⟨none, [], pw2.1, σ.registers, σ.regUsage, [(ptr, d)]⟩

/-- **`read_register`'s answer function**: the charge chain computed from `σ`. -/
def ansReadRegister (σ : St) (id ptr memSz : Nat) : HAns :=
  let dr := (Array.find? (fun x => decide (x.fst = id)) σ.registers).map (·.2)
  let n := (dr.getD ByteArray.empty).size
  let p1 := payBase σ.gas C.base
  let pr1 := payBase p1.1 C.readRegisterBase
  let pr2 := payPer pr1.1 C.readRegisterByte n
  let pw1 := payBase pr2.1 C.writeMemoryBase
  let pw2 := payPer pw1.1 C.writeMemoryByte n
  ansReadRegisterG σ id ptr memSz dr p1 pr1 pr2 pw1 pw2


theorem regGetH_none {s : St} {id : Nat} (hf : Array.find? (fun x => decide (x.fst = id)) s.registers = none) :
    (regGetH id).run s = .error (invErr id) s := by
  unfold regGetH
  rewrite [bind_ok (hmGet_run _)]
  simp only [hf]
  rfl

theorem regGetH_e1 {s : St} {id k : Nat} {d : ByteArray} {g : Gas} {e : String}
    (hf : Array.find? (fun x => decide (x.fst = id)) s.registers = some (k, d))
    (h : payBase s.gas C.readRegisterBase = (g, some e)) :
    (regGetH id).run s = .error e { s with gas := g } := by
  unfold regGetH
  rewrite [bind_ok (hmGet_run _)]
  simp only [hf]
  exact bind_err (payBaseH_err' h)

theorem regGetH_e2 {s : St} {id k : Nat} {d : ByteArray} {g g' : Gas} {e : String}
    (hf : Array.find? (fun x => decide (x.fst = id)) s.registers = some (k, d))
    (h : payBase s.gas C.readRegisterBase = (g, none))
    (h' : payPer g C.readRegisterByte d.size = (g', some e)) :
    (regGetH id).run s = .error e { s with gas := g' } := by
  unfold regGetH
  rewrite [bind_ok (hmGet_run _)]
  simp only [hf]
  rewrite [bind_ok (payBaseH_ok' h)]
  exact bind_err (payPerH_err' (t := { s with gas := g }) h')

theorem regGetH_ok' {s : St} {id k : Nat} {d : ByteArray} {g g' : Gas}
    (hf : Array.find? (fun x => decide (x.fst = id)) s.registers = some (k, d))
    (h : payBase s.gas C.readRegisterBase = (g, none))
    (h' : payPer g C.readRegisterByte d.size = (g', none)) :
    (regGetH id).run s = .ok d { s with gas := g' } :=
  regGetH_ok hf (payBaseH_ok' h) (payPerH_ok' (t := { s with gas := g }) h')

theorem writeMemH_e1 {s : St} {ptr : Nat} {d : ByteArray} {g : Gas} {e : String}
    (h : payBase s.gas C.writeMemoryBase = (g, some e)) :
    (writeMemH ptr d).run s = .error e { s with gas := g } := by
  rewrite [writeMemH_unfold]
  exact bind_err (payBaseH_err' h)

theorem writeMemH_e2 {s : St} {ptr : Nat} {d : ByteArray} {g g' : Gas} {e : String}
    (h : payBase s.gas C.writeMemoryBase = (g, none)) (h' : payPer g C.writeMemoryByte d.size = (g', some e)) :
    (writeMemH ptr d).run s = .error e { s with gas := g' } := by
  rewrite [writeMemH_unfold, bind_ok (payBaseH_ok' h), writeTail]
  exact bind_err (payPerH_err' (t := { s with gas := g }) h')

/-- **`read_register` after the pop**, with the charges' results as parameters. -/
theorem read_register_tailG (t : St) (id ptr : Nat) (r? : Option (Nat × ByteArray))
    (p1 pr1 pr2 pw1 pw2 : Gas × Option String)
    (hfd : Array.find? (fun x => decide (x.fst = id)) t.registers = r?)
    (h1 : payBase t.gas C.base = p1) (h2 : payBase p1.1 C.readRegisterBase = pr1)
    (h3 : payPer pr1.1 C.readRegisterByte ((r?.map (·.2)).getD ByteArray.empty).size = pr2)
    (h4 : payBase pr2.1 C.writeMemoryBase = pw1)
    (h5 : payPer pw1.1 C.writeMemoryByte ((r?.map (·.2)).getD ByteArray.empty).size = pw2) :
    (((payBaseH C.base) >>= fun _ => (regGetH id) >>= fun d => writeMemH ptr d) : HM Unit).run t =
      runOf t (ansReadRegisterG t id ptr (memBytes t) (r?.map (·.2)) p1 pr1 pr2 pw1 pw2) := by
  unfold ansReadRegisterG
  rcases p1 with ⟨g1, _ | e1⟩
  case some => rewrite [bind_err (payBaseH_err' h1)]; rfl
  rewrite [bind_ok (payBaseH_ok' h1), bind_run]
  rcases r? with _ | ⟨k, d⟩
  · rewrite [regGetH_none (s := { t with gas := g1 }) hfd]
    rfl
  simp only [Option.map, Option.getD] at h3 h5
  dsimp only at h2 h3 h5 ⊢
  rcases pr1 with ⟨g2, _ | e2⟩
  case some => rewrite [regGetH_e1 (s := { t with gas := g1 }) hfd h2]; rfl
  rcases pr2 with ⟨g3, _ | e3⟩
  case some => rewrite [regGetH_e2 (s := { t with gas := g1 }) hfd h2 h3]; rfl
  rewrite [regGetH_ok' (s := { t with gas := g1 }) hfd h2 h3]
  dsimp only at h4 h5 ⊢
  rcases pw1 with ⟨g4, _ | e4⟩
  case some => rewrite [writeMemH_e1 (s := { t with gas := g3 }) h4]; rfl
  rcases pw2 with ⟨g5, _ | e5⟩
  case some => rewrite [writeMemH_e2 (s := { t with gas := g3 }) h4 h5]; rfl
  by_cases hm : ptr + d.size > memBytes t
  · rewrite [writeMemH_mav (s := { t with gas := g3 }) (payBaseH_ok' h4)
      (payPerH_ok' (t := { t with gas := g4 }) h5) hm]
    simp only [Option.map, Option.isSome, Bool.false_eq_true, ite_false, hm, ite_true]
    rfl
  · rewrite [writeMemH_ok (s := { t with gas := g3 }) (payBaseH_ok' h4)
      (payPerH_ok' (t := { t with gas := g4 }) h5) hm]
    simp only [Option.map, Option.isSome, Bool.false_eq_true, ite_false, hm]
    unfold runOf postOf
    simp only [List.foldl, HostFoot.writeBytes_split]

/-- **`read_register`'s arm is its answer function**, every branch, from the post-pop state
`s0` with arguments `args = (id, ptr)` (`(popArgs 2).run s = .ok args s0`). -/
theorem read_register_ans {s s0 : St} {args : Vector Nat 2} (e0 : (popArgs 2).run s = .ok args s0) :
    (hostCall "read_register").get!.run s = runOf s0 (ansReadRegister s0 args[0] args[1] (memBytes s0)) := by
  rewrite [read_register_h]; simp only [Option.get!]
  rewrite [bind_ok e0]
  exact read_register_tailG _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl

#print axioms register_len_ans
#print axioms input_ans
#print axioms read_register_ans

end HostAns
end WasmBase
