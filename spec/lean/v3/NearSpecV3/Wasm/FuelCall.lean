import NearSpecV3.Wasm.FuelSuff
/-!
# Fuel sufficiency (W02): from one entry to a whole call

`Wasm/FuelSuff.lean` proves `callEntry_stable`: above `wasmFuel cfg prepaid` the result of one
`callEntry` does not depend on the fuel. Here the `prepaid` of every entry state of `runCall` is
tied to the call's `ctx.prepaidGas`: loading charges, `instantiate` and a finished `start` run keep
it. The result, `runCallWithLimits_stable`, is the statement the successor's
`StorageExecution.functionCall` needs: with `wasmFuel cfg gas` its call has the result it has with
any larger budget, so fuel exhaustion never decides a verdict.
-/
namespace NearSpecV3.Wasm.FuelGen

/-! ## Finishing a run keeps the gas -/

theorem doReturn_fin {p : Prepared} {s s' : St} (h : doReturn p s = .fin s') : s'.gas = s.gas := by
  unfold doReturn at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h; rfl
      · cases h

theorem doBr_fin {p : Prepared} {s s' : St} {f : Frame} {l : Nat} (h : doBr p s f l = .fin s') :
    s'.gas = s.gas := by
  unfold doBr at h
  split at h
  · exact doReturn_fin h
  · split at h
    · cases h
    · cases h

theorem callHost_fin {s s' : St} {name : String} (h : callHost s name = .fin s') : False := by
  unfold callHost at h
  repeat' split at h
  all_goals cases h

theorem charge_fin {s s' : St} {fee : Fee} {c : Nat} (h : charge s fee c = .fin s') : False := by
  unfold charge at h
  dsimp only at h
  repeat' split at h
  all_goals cases h

theorem enter_fin {p : Prepared} {s s' : St} {fi : Nat} (h : enter p s fi = .fin s') : False := by
  unfold enter at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | cases h
    | exact charge_fin h

theorem callFunc_fin {cfg : NearCfg} {p : Prepared} {s s' : St} {fi : Nat}
    (h : callFunc cfg p s fi = .fin s') : False := by
  unfold callFunc at h
  split at h
  · exact callHost_fin h
  · exact enter_fin h

theorem memCopy_fin {s s' : St} {d src n : Nat} (h : memCopy s d src n = .fin s') : False := by
  unfold memCopy at h; split at h <;> cases h

theorem memInit_fin {s s' : St} {seg d src n : Nat} (h : memInit s seg d src n = .fin s') : False := by
  unfold memInit at h; dsimp only at h; split at h <;> cases h

theorem memFill_fin {s s' : St} {d v n : Nat} (h : memFill s d v n = .fin s') : False := by
  unfold memFill at h; split at h
  · cases h
  · simp only [Id.run_bind, Id.run_pure] at h; cases h

theorem tableInit_fin {s s' : St} {seg d src n : Nat} (h : tableInit s seg d src n = .fin s') :
    False := by
  unfold tableInit at h; dsimp only at h; split at h
  · cases h
  · simp only [Id.run_bind, Id.run_pure] at h; cases h

set_option maxHeartbeats 4000000 in
/-- `exec` finishes only by returning from the last frame, which leaves the gas alone. -/
theorem exec_fin (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (i : Instr)
    (s' : St) (h : exec cfg p s f pf i = .fin s') : s'.gas = s.gas := by
  cases i <;> simp only [exec] at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; done)
    | exact doReturn_fin h
    | exact (doBr_fin h).trans (by simp [popN_snd])
    | exact (callFunc_fin h).elim
    | exact (memCopy_fin h).elim
    | exact (memFill_fin h).elim
    | exact (memInit_fin h).elim
    | exact (tableInit_fin h).elim
    | (simp only [Id.run_bind, Id.run_pure] at h; cases h; done)

def stepVal {β : Type} : ForInStep β → β
  | .done x => x
  | .yield x => x

theorem forIn_list_inv {α β ε : Type} (f : α → β → Except ε (ForInStep β)) (P : β → Prop)
    (hf : ∀ a b r, P b → f a b = .ok r → P (stepVal r)) :
    ∀ (l : List α) (b : β) (r : β), P b → forIn l b f = .ok r → P r
  | [], b, r, hb, h => by
    simp only [List.forIn_nil] at h
    cases h; exact hb
  | a :: l, b, r, hb, h => by
    rw [List.forIn_cons] at h
    cases hfa : f a b with
    | error e => rw [hfa] at h; cases h
    | ok x =>
      rw [hfa] at h
      have hx := hf a b x hb hfa
      cases x with
      | done y => cases h; exact hx
      | yield y => exact forIn_list_inv f P hf l y r hx h

theorem forIn_array_inv {α β ε : Type} (xs : Array α) (f : α → β → Except ε (ForInStep β))
    (P : β → Prop) (hf : ∀ a b r, P b → f a b = .ok r → P (stepVal r)) (b r : β) (hb : P b)
    (h : forIn xs b f = .ok r) : P r := by
  rw [← Array.forIn_toList] at h
  exact forIn_list_inv f P hf _ b r hb h

theorem instantiate_gas {cfg : NearCfg} {p : Prepared} {gas : Gas} {s : St}
    (h : instantiate cfg p gas = .ok s) : s.gas = gas := by
  unfold instantiate at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · cases h
    · rename_i w hw
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have h1 : v.1.gas = gas := by
        refine forIn_array_inv _ _ (fun st => st.1.gas = gas) ?_ _ _ rfl hv
        intro a b r hb hfab
        try simp only at hfab
        repeat' split at hfab
        all_goals (first
          | (cases hfab; done)
          | (simp only [pure, Except.pure, Except.ok.injEq] at hfab; subst hfab; simp only [stepVal]; first
              | exact hb
              | (rw [← hb]; exact congrArg Prod.snd (fg_tableInit (by assumption)))))
      refine forIn_array_inv _ _ (fun st => st.1.gas = gas) ?_ _ _ h1 hw
      intro a b r hb hfab
      try simp only at hfab
      repeat' split at hfab
      all_goals (first
        | (cases hfab; done)
        | (simp only [pure, Except.pure, Except.ok.injEq] at hfab; subst hfab; simp only [stepVal]; first
            | exact hb
            | (rw [← hb]; exact congrArg Prod.snd (fg_memInit (by assumption)))))

theorem charge_cont_prepaid {s s1 : St} {fee : Fee} {c : Nat} (h : charge s fee c = .cont s1) :
    s1.gas.prepaid = s.gas.prepaid := by
  obtain ⟨-, rfl⟩ := charge_cont' h; rfl

/-- A step that finishes keeps `prepaid`. -/
theorem step_fin_prepaid {cfg : NearCfg} {p : Prepared} {G : Nat} {s s' : St}
    (hI : Inv cfg p G s) (h : step cfg p s = .fin s') : s'.gas.prepaid = G := by
  obtain ⟨-, hG, f, fs, hfr, -, -⟩ := hI
  unfold step at h
  rw [hfr] at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rw [exec_fin _ _ _ _ _ _ _ h]; exact hG
      · split at h
        · rename_i s1 hc
          rw [exec_fin _ _ _ _ _ _ _ h, charge_cont_prepaid hc]; exact hG
        · exact (charge_fin h).elim

theorem run_fin_prepaid {cfg : NearCfg} {p : Prepared} {G : Nat} (hr : 0 < cfg.regularOpCost)
    (hfn : ∀ (j : Nat) (pf : PFunc), p.funcs[j]? = some pf → FnOK cfg pf) (hh : HostsOK) :
    ∀ (n : Nat) (s s' : St), Inv cfg p G s → run cfg p n s = .fin s' → s'.gas.prepaid = G
  | 0, _, _, _, h => by simp [run] at h
  | n + 1, s, s', hI, h => by
    simp only [run] at h
    cases hs : step cfg p s with
    | cont s1 =>
      rw [hs] at h
      exact run_fin_prepaid hr hfn hh n s1 s' (step_post hr hfn hh hI hs).1 h
    | fin s2 => rw [hs] at h; cases h; exact step_fin_prepaid hI hs
    | abort _ _ => rw [hs] at h; cases h
    | unmodeled _ => rw [hs] at h; cases h

theorem sync_prepaid {s s3 : St} (h : sync s = .ok s3) : s3.gas.prepaid = s.gas.prepaid := by
  unfold sync at h
  dsimp only at h
  split at h
  · cases h; rfl
  · split at h
    · rename_i gs hb
      cases h
      unfold burn at hb
      dsimp only at hb
      split at hb
      · simp at hb
      · split at hb
        · simp only [Prod.mk.injEq] at hb; obtain ⟨rfl, -⟩ := hb; rfl
        · unfold processGasLimit at hb; simp at hb
    · cases h

/-- The state an entry starts `run` from satisfies the invariant. -/
theorem entry_inv {cfg : NearCfg} {p : Prepared}
    (hfn : ∀ (j : Nat) (pf : PFunc), p.funcs[j]? = some pf → FnOK cfg pf) {s s1 : St} {fi : Nat}
    (he : enter p { s with gas := { s.gas with g := s.gas.remaining }, stack := #[], frames := [] } fi
      = .cont s1) :
    Inv cfg p s.gas.prepaid s1 := by
  obtain ⟨pf2, hpf2, fr, hfr, hfn2, hpc2, hlab2, hle, hrem, hG⟩ := enter_cont he
  obtain ⟨enc2, hn2, hw2, hfc2⟩ := hfn _ _ hpf2
  have hpf2' : p.funcs[fr.fn]? = some pf2 := by rw [hfn2]; exact hpf2
  refine ⟨?_, hG, fr, [], hfr, ⟨pf2, enc2, hpf2', hfc2, hn2, hw2, by rw [hpc2]; exact .entry,
    by rw [hpc2, hn2.zero]; exact hlab2⟩, by simp⟩
  rw [hrem]; exact hle

/-- A `callEntry` that finishes without error keeps `prepaid`. -/
theorem callEntry_prepaid {cfg : NearCfg} {p : Prepared} (hr : 0 < cfg.regularOpCost)
    (hfn : ∀ (j : Nat) (pf : PFunc), p.funcs[j]? = some pf → FnOK cfg pf) (hh : HostsOK)
    {n : Nat} {s s' : St} {fi : Nat} (h : callEntry cfg p n s fi = .ok (s', none)) :
    s'.gas.prepaid = s.gas.prepaid := by
  unfold callEntry at h
  simp only at h
  cases he : enter p { s with gas := { s.gas with g := s.gas.remaining }, stack := #[], frames := [] } fi with
  | cont s1 =>
    rw [he] at h
    simp only at h
    have hI := entry_inv hfn he
    cases hrun : run cfg p n s1 with
    | fin s2 =>
      rw [hrun] at h
      simp only at h
      cases hs : sync s2 with
      | error _ => rw [hs] at h; cases h
      | ok s3 =>
        rw [hs] at h
        simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rw [sync_prepaid hs]
        exact run_fin_prepaid hr hfn hh n s1 s2 hI hrun
    | abort s2 e =>
      rw [hrun] at h
      simp only at h
      cases hs : sync s2 with
      | error _ => rw [hs] at h; cases h
      | ok s3 => rw [hs] at h; simp [Except.map] at h
    | unmodeled _ => rw [hrun] at h; cases h
    | cont _ => rw [hrun] at h; cases h
  | fin s2 => exact (enter_fin he).elim
  | abort s2 e =>
    rw [he] at h
    simp only at h
    cases hs : sync s2 with
    | error _ => rw [hs] at h; cases h
    | ok s3 => rw [hs] at h; simp [Except.map] at h
  | unmodeled _ => rw [he] at h; cases h

/-! ## Loading charges keep `prepaid` -/

theorem burn_prepaid (gs : Gas) (x : Nat) : (burn gs x).1.prepaid = gs.prepaid := by
  unfold burn; dsimp only
  split
  · rfl
  · split
    · rfl
    · unfold processGasLimit; rfl

theorem payPer_prepaid (gs : Gas) (c : Cost) (n : Nat) : (payPer gs c n).1.prepaid = gs.prepaid := by
  unfold payPer
  split
  · rfl
  · dsimp only; exact burn_prepaid _ _

theorem gasInit_prepaid (x : Nat) : (Gas.init x).prepaid = x := rfl

theorem loadPrepaid (gs0 : Gas) (c c' : Cost) (n : Nat) :
    (match payPer gs0 c n with
      | (gs, none) => payBase gs c'
      | r => r).1.prepaid = gs0.prepaid := by
  split
  · rename_i gs1 hp1
    have h2 := congrArg (fun x => x.1.prepaid) hp1
    simp only [payPer_prepaid] at h2
    simp only [payBase, payPer_prepaid]; exact h2.symm
  · rename_i r hne
    rw [payPer_prepaid]

/-! ## The whole call -/

/-- `runTail` (start entry, then the method) does not depend on the fuel above
`wasmFuel cfg prepaid`. -/
theorem runTail_stable {cfg : NearCfg} {p : Prepared} (hr : 0 < cfg.regularOpCost)
    (hfn : ∀ (j : Nat) (pf : PFunc), p.funcs[j]? = some pf → FnOK cfg pf) (hh : HostsOK)
    (S : St) (mi : Nat) (start : Option Nat) (n k : Nat) (hn : wasmFuel cfg S.gas.prepaid ≤ n) :
    runTail cfg p (n + k) S mi start = runTail cfg p n S mi start := by
  cases start with
  | none =>
    simp only [runTail]
    rw [callEntry_stable hr hfn hh S mi n k hn]
  | some st =>
    simp only [runTail]
    rw [callEntry_stable hr hfn hh S st n k hn]
    cases hc : callEntry cfg p n S st with
    | error _ => rfl
    | ok r =>
      obtain ⟨s1, e⟩ := r
      cases e with
      | some _ => rfl
      | none =>
        simp only
        rw [callEntry_stable hr hfn hh s1 mi n k (by rw [callEntry_prepaid hr hfn hh hc]; exact hn)]

/-- **Fuel sufficiency for a call.** If every function `prepare` produces satisfies `FnOK` and the
host arms are `HostsOK`, then `runCall` with fuel at least `wasmFuel cfg ctx.prepaidGas` has the
same result as with any larger fuel. -/
theorem runCall_stable {cfg : NearCfg} (hr : 0 < cfg.regularOpCost) (hh : HostsOK)
    (code : ByteArray) (blockLevel : Bool)
    (hP : ∀ p, prepare cfg code blockLevel = .ok p →
      ∀ (j : Nat) (pf : PFunc), p.funcs[j]? = some pf → FnOK cfg pf)
    (method : String) (ctx : CallCtx) (n k : Nat) (hn : wasmFuel cfg ctx.prepaidGas ≤ n)
    (full : Bool) (real : Option TTN.RealStore) :
    runCall cfg code method ctx (n + k) blockLevel full real =
      runCall cfg code method ctx n blockLevel full real := by
  simp only [runCall]
  by_cases hm : method.isEmpty = true
  · simp only [hm, ite_true]
  simp only [hm, Bool.false_eq_true, ite_false]
  cases hp : prepare cfg code blockLevel <;> simp only
  rename_i p
  have hfn := hP p hp
  split
  · rfl
  split
  · rfl
  rename_i gs hl
  have hgs : gs.prepaid = ctx.prepaidGas := by
    have h1 := congrArg (fun x => x.1.prepaid) hl
    rw [← h1]; exact (loadPrepaid _ _ _ _).trans (gasInit_prepaid _)
  split
  · rfl
  · rfl
  split
  · rfl
  · rfl
  · rfl
  rename_i mi hres
  split
  · rfl
  rename_i S hinst
  exact runTail_stable hr hfn hh _ mi p.m.start n k (by
    show wasmFuel cfg S.gas.prepaid ≤ n
    rw [instantiate_gas hinst, hgs]; exact hn)

theorem runCallWithLimits_stable {cfg : NearCfg} (hr : 0 < cfg.regularOpCost) (hh : HostsOK)
    (code : ByteArray) (blockLevel : Bool)
    (hP : ∀ p, prepare cfg code blockLevel = .ok p →
      ∀ (j : Nat) (pf : PFunc), p.funcs[j]? = some pf → FnOK cfg pf)
    (method : String) (ctx : CallCtx) (n k : Nat) (hn : wasmFuel cfg ctx.prepaidGas ≤ n)
    (full : Bool) (real : Option TTN.RealStore) :
    runCallWithLimits cfg code method ctx (n + k) blockLevel full real =
      runCallWithLimits cfg code method ctx n blockLevel full real := by
  simp only [runCallWithLimits]
  split
  · exact runCall_stable hr hh code blockLevel hP method ctx n k hn full real
  · split
    · split
      · exact runCall_stable hr hh code blockLevel hP method ctx n k hn full real
      · rfl
    · exact runCall_stable hr hh code blockLevel hP method ctx n k hn full real

end NearSpecV3.Wasm.FuelGen

#print axioms NearSpecV3.Wasm.FuelGen.runCallWithLimits_stable
