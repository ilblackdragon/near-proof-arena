import WasmBase.Main.HostWriteCov

/-!
# WasmBase.Main.HostWriteCovCheck — non-vacuity of the A-T1 write coverage (E2E A-T1, WCOV)

1. **AIR** — an explicit `HOSTB` response group of an `attached_deposit` call (16 bytes at
   `ptr = 100`, `wcnt = 1` on every row): its write pairs consume a space-3 message at every address
   `100 … 115` (`wgroup_cov`), produce the written bytes there at `ts` (`wgroup_prod`), and the old
   `HOSTB` interactions alone (the pre-A-T1 shape) consume nothing on the CH bus (`wgroup_old_nocov`).
2. **Producer clause** — `HostNoTouch` is what an honest `attached_deposit` call satisfies: its arm
   writes only the 16 bytes `[ptr, ptr + 16)` (`attached_deposit_frame`, `callHost_attached_deposit_frame`),
   so with those 16 addresses consumed (the A-T1 rows, `wgroup_cov`) the clause holds at **every**
   witness at such a call (`hostNoTouch_attached_deposit`, no premise on the state beyond `PagesOK`
   and the code facts).  The pre-A-T1 shape consumes none of the 16 addresses (`wgroup_old_nocov`),
   so this route to the clause is closed for it (and the clause itself fails there whenever the call
   changes a byte, since the twin with that byte perturbed sees the write).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
open HostFoot TwoRun HostIf
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. AIR: an explicit write group -/

/-- One `HOSTB` row of the group: response byte `i` (`dir = 1`, `reg = 0`, `act = 1`) of a 16-byte
group at `ptr = 100`, call time `ts = 10`, old bytes `0` produced at `mtp = 5`, new byte `i + 1`. -/
def wcell (r c : Nat) : F :=
  if c = HostB.ts then 10 else if c = HostB.dir then 1 else if c = HostB.pos then (r : F)
  else if c = HostB.bv then ((r + 1 : Nat) : F) else if c = HostB.blen then 16
  else if c = HostB.hid then 21 else if c = HostB.gap then ((15 - r : Nat) : F)
  else if c = HostB.act then 1 else if c = HostB.f then (if r = 0 then 1 else 0)
  else if c = HostB.ptrLo then 100 else if c = HostB.mtp then 5 else 0

def wtr : Trace := ⟨fun t => if t = 25 then 16 else 0, fun t r c => if t = 25 then wcell r c else 0⟩

/-- The group's consumed write messages. -/
def wcons : List Msg := (List.range 16).flatMap (rowCons HostBW wtr [] 25)

theorem wgroup_cons : wcons = (List.range 16).map (fun i => ⟨3, 100 + i, 0, 0, 0, 0, 0, 5⟩) := by decide +kernel

/-- **Every written address is consumed** by the group's write pairs. -/
theorem wgroup_cov : ∀ i, i < 16 → Cov3 wcons (100 + i) := by
  intro i hi
  rw [wgroup_cons]
  exact ⟨⟨3, 100 + i, 0, 0, 0, 0, 0, 5⟩, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, rfl, rfl⟩

/-- The group produces the written bytes at the call time. -/
theorem wgroup_prod : (List.range 16).flatMap (rowProd HostBW wtr [] 25) =
    (List.range 16).map (fun i => ⟨3, 100 + i, 0, i + 1, 0, 0, 0, 10⟩) := by decide +kernel

/-- **The pre-A-T1 shape**: `HOSTB`'s own interactions carry no CH message for response bytes. -/
theorem wgroup_old_nocov : (List.range 16).flatMap (rowCons HostB.table wtr [] 25) = [] ∧
    (List.range 16).flatMap (rowProd HostB.table wtr [] 25) = [] := by decide +kernel

/-- The A-T1 table's CH traffic on the group is exactly the write pairs. -/
theorem wgroup_bk : (List.range 16).flatMap (rowCons HostBK.table wtr [] 25) = wcons := by decide +kernel

/-! ## 2. The honest `attached_deposit` call writes exactly `[ptr, ptr + 16)` -/

theorem readByte_writeBytes_out {s : St} (hP : PagesOK s) (ptr : Nat) (d : ByteArray) {a : Nat}
    (ha : ¬ (ptr ≤ a ∧ a < ptr + d.size)) : readByte (writeBytes s ptr d) a = readByte s a := by
  rw [writeBytes_eq]
  have key : ∀ (l : List Nat) (u : St), PagesOK u → (∀ i ∈ l, ptr + i ≠ a) →
      readByte (l.foldl (fun s i => writeByte s (ptr + i) d[i]!) u) a = readByte u a ∧
        PagesOK (l.foldl (fun s i => writeByte s (ptr + i) d[i]!) u) := by
    intro l
    induction l with
    | nil => intro u hu _; exact ⟨rfl, hu⟩
    | cons i l ih =>
      intro u hu hl
      simp only [List.foldl_cons]
      obtain ⟨h1, h2⟩ := ih (writeByte u (ptr + i) d[i]!) (writeByte_ok hu _ _)
        (fun j hj => hl j (List.mem_cons_of_mem _ hj))
      refine ⟨?_, h2⟩
      rw [h1, readByte_writeByte' hu]
      have : ptr + i ≠ a := hl i List.mem_cons_self
      simp [this]
  exact (key _ s hP (fun i hi h => ha (by simp [List.mem_range'] at hi; omega))).1

theorem natLE_size (n w : Nat) : (natLE n w).size = w := by
  simp [natLE, ByteArray.size]


theorem run_bind_ok_inv {α β : Type} {x : HM α} {f : α → HM β} {t t' : St} {b : β}
    (h : (x >>= f).run t = .ok b t') : ∃ a s, x.run t = .ok a s ∧ (f a).run s = .ok b t' := by
  rw [bind_run] at h
  cases hx : x.run t with
  | ok a s => rw [hx] at h; exact ⟨a, s, rfl, h⟩
  | error e s => rw [hx] at h; cases h

theorem withGas_pages {f : Gas → Gas × Option String} {t t' : St} {v : Unit}
    (h : (withGas f).run t = .ok v t') : t'.pages = t.pages := by
  rw [withGas_run] at h
  split at h
  · cases h
  · cases h; rfl

/-- The `attached_deposit` arm. -/
def adArm : HM Unit := do let a ← popArgs 1; payBaseH C.base; setU128H a[0] (← get).ctx.attachedDeposit
theorem attached_deposit_arm : hostCall "attached_deposit" = some adArm := rfl

/-- **The `attached_deposit` arm writes exactly `[ptr, ptr + 16)`**: a successful run keeps the page
count and every byte outside the 16 bytes at the popped pointer. -/
theorem attached_deposit_frame {t t' : St} (hP : PagesOK t)
    (h : adArm.run t = .ok () t') :
    t'.pages.size = t.pages.size ∧
      ∀ a, ¬ (topArg t ≤ a ∧ a < topArg t + 16) → readByte t' a = readByte t a := by
  unfold adArm at h
  obtain ⟨av, t1, h1, h⟩ := run_bind_ok_inv h
  rw [popArgs1_run] at h1
  cases h1
  obtain ⟨_, t2, h2, h⟩ := run_bind_ok_inv h
  unfold payBaseH at h2
  have p2 := withGas_pages h2
  obtain ⟨st, t3, h3, h⟩ := run_bind_ok_inv h
  rw [hmGet_run] at h3
  cases h3
  unfold setU128H writeMemH at h
  obtain ⟨_, t4, h4, h⟩ := run_bind_ok_inv h
  unfold payBaseH at h4
  have p4 : t4.pages = t2.pages := withGas_pages h4
  obtain ⟨_, t5, h5, h⟩ := run_bind_ok_inv h
  unfold payPerH at h5
  have p5 : t5.pages = t4.pages := withGas_pages h5
  obtain ⟨st5, t6, h6, h⟩ := run_bind_ok_inv h
  rw [hmGet_run] at h6
  cases h6
  split at h
  · obtain ⟨_, t7, h7, -⟩ := run_bind_ok_inv h
    cases h7
  · rw [hmSet_run] at h
    cases h
    have e5 : t5.pages = t.pages := by rw [p5, p4, p2]
    have hP5 : PagesOK t5 := fun i hi => by
      have := hP i (by rw [← e5]; exact hi); simpa only [e5] using this
    refine ⟨by rw [StepPages.writeBytes_size, e5], fun a ha => ?_⟩
    rw [readByte_writeBytes_out hP5 _ _ (by rw [natLE_size]; exact ha), readByte_congr e5]

#print axioms attached_deposit_frame

theorem pagesOK_of_eq {s s' : St} (h : s'.pages = s.pages) (hs : PagesOK s) : PagesOK s' := by
  unfold PagesOK at hs ⊢; rw [h]; exact hs

/-- `callHost` through its guard, `sync` and the arm table, for an abstract arm `m`. -/
theorem callHost_arm {s s1 y : St} {name : String} {m : HM Unit}
    (hg : (s.real.isSome && realOodHosts.contains name &&
      !(s.globalActions && globalPromiseHosts.contains name)) = false)
    (hs : sync s = .ok s1) (hd : dispatchArm s1 name = some m) (h : callHost s name = .cont y) :
    ∃ u s2, m.run s1 = .ok u s2 ∧ y = { s2 with gas := { s2.gas with g := s2.gas.remaining } } := by
  unfold callHost at h
  rw [if_neg (by rw [hg]; decide)] at h
  simp only [hs, hd] at h
  revert h
  cases m.run s1 with
  | ok u s2 => intro h; cases h; exact ⟨u, s2, rfl, rfl⟩
  | error e s2 =>
    intro h
    simp only at h
    by_cases hu : e.startsWith "unmodeled" = true
    · rw [if_pos hu] at h; cases h
    · rw [if_neg hu] at h; cases h

/-- **`callHost` of `attached_deposit` writes only `[ptr, ptr + 16)`** (`ptr` the top stack word). -/
theorem callHost_attached_deposit_frame {s y : St} (hP : PagesOK s)
    (h : callHost s "attached_deposit" = .cont y) :
    ∀ a, ¬ (topArg s ≤ a ∧ a < topArg s + 16) → readByte y a = readByte s a := by
  intro a ha
  have hg : (s.real.isSome && realOodHosts.contains "attached_deposit" &&
      !(s.globalActions && globalPromiseHosts.contains "attached_deposit")) = false := by
    have : realOodHosts.contains "attached_deposit" = false := by decide
    rw [this]; simp
  cases hs : sync s with
  | error e =>
    unfold callHost at h
    rw [if_neg (by rw [hg]; decide), hs] at h
    cases h
  | ok s1 =>
    have hv := sync_st hs
    have e1 : s1.pages = s.pages := congrArg Vis.pages hv
    have e2 : s1.stack = s.stack := congrArg Vis.stack hv
    obtain ⟨u, s2, hrun, rfl⟩ := callHost_arm hg hs attached_deposit_arm h
    have hfr := attached_deposit_frame (pagesOK_of_eq e1 hP) hrun
    have ht : topArg s1 = topArg s := by simp only [topArg, e2]
    rw [ht] at hfr
    exact (hfr.2 a ha).trans (readByte_congr e1 a)

#print axioms callHost_attached_deposit_frame

/-- **An honest `attached_deposit` call satisfies `HostNoTouch`** as soon as the row consumes the 16
addresses `[ptr, ptr + 16)` (`ptr` the top stack word at the call) — which the A-T1 `HOSTB` write rows
do (`wgroup_cov`). -/
theorem hostNoTouch_attached_deposit {X : Ctx} {cons : List Msg} {w : St} {f : Frame} {rest : List Frame}
    {pf : PFunc} {fi : Nat} (hfr : w.frames = f :: rest) (hpf : X.p.funcs[f.fn]? = some pf)
    (hcode : pf.code[f.pc]? = some (.call fi)) (himp : fi < X.p.m.imports.size)
    (hname : X.p.m.imports[fi].name = "attached_deposit")
    (hlin : ∀ kd fee, pf.gas[f.pc]? = some (some (kd, fee)) → kd ≠ .linear) (hP : PagesOK w)
    (hcov : ∀ i, i < 16 → Cov3 cons (topArg w + i)) : HostNoTouch X cons w := by
  intro a ha v y hy
  have hout : ¬ (topArg w ≤ a ∧ a < topArg w + 16) := by
    rintro ⟨h1, h2⟩
    have := hcov (a - topArg w) (by omega)
    rw [show topArg w + (a - topArg w) = a by omega] at this
    exact ha this
  have hfru : (writeByte w a v).frames = f :: rest := hfr
  have hPu := writeByte_ok hP a v
  have fin : ∀ u1 : St, u1.pages = (writeByte w a v).pages → u1.stack = w.stack → u1.frames = f :: rest →
      callHost (setFrame u1 { f with pc := f.pc + 1 }) "attached_deposit" = .cont y →
      readByte y a = readByte (writeByte w a v) a := by
    intro u1 hp hs hf hc
    obtain ⟨-, hs1, hp1, -, -⟩ := setFrame_cons (s := u1) hf { f with pc := f.pc + 1 }
    have hPs : PagesOK (setFrame u1 { f with pc := f.pc + 1 }) := pagesOK_of_eq (hp1.trans hp) hPu
    have ht : topArg (setFrame u1 { f with pc := f.pc + 1 }) = topArg w := by simp only [topArg, hs1, hs]
    have h := callHost_attached_deposit_frame hPs hc a (by rw [ht]; exact hout)
    rw [h]; exact readByte_congr (hp1.trans hp) a
  obtain ⟨n1, n2⟩ := TwoRun.step_call X.cfg X.p hfru hpf hcode himp hname
  cases hg : pf.gas[f.pc]? with
  | none =>
    exfalso
    unfold step at hy; rw [hfru] at hy; simp only [hpf, hcode, hg] at hy; cases hy
  | some o =>
    cases o with
    | none =>
      rw [n1 hg] at hy
      exact fin _ rfl rfl hfru hy
    | some kf =>
      obtain ⟨kd, fee⟩ := kf
      rw [n2 kd fee (hlin kd fee hg) hg] at hy
      cases hc : charge (writeByte w a v) fee 0 with
      | cont s1 =>
        rw [hc] at hy
        dsimp only at hy
        have hL : Low (fun _ => False) 0 (writeByte w a v) (writeByte w a v) :=
          ⟨rfl, Nat.zero_le _, Nat.zero_le _, rfl, ⟨hPu, hPu, rfl, fun _ h => h.elim⟩⟩
        obtain ⟨G, rfl, -⟩ := charge_two hL fee hc
        exact fin { writeByte w a v with gas := G } rfl rfl hfru hy
      | _ => rw [hc] at hy; cases hy

#print axioms hostNoTouch_attached_deposit
#print axioms wgroup_cov
#print axioms wgroup_old_nocov

end WasmBase
