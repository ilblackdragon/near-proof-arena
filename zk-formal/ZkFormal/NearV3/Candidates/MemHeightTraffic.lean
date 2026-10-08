import ZkFormal.NearV3.Candidates.MemHeight
import ZkFormal.NearV3.Sched.Complete.MemTraffic
namespace ZkFormal.NearV3.Candidates.MemHeight
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
theorem mem_row_count (R : Run) (hg : ∀ g ∈ R.segs, SegOk g) (t r : Nat) (pub : List Fp)
    (hr : r < (trace R).height t) (b : Nat) (send : Bool) (m : List Fp) :
    (Mem.interactions.map fun i =>
      if i.bus = b ∧ i.send = send ∧ i.msgVal (trace R) t r pub = m then
        i.multNat (trace R) t r pub else 0).sum =
      (fmsgs (rowMsgs b send (vsAt R.segs r))).count m := by
  have hs : ∀ g ∈ R.segs, SegSmall g := fun g h => (hg g h).small
  have hx := (vsAt_ok R.segs hg r).1
  have hcur := mem_cur R hg hr pub
  have ec0 : ∀ c, (ZkFormal.Chacha.Table.E.c c).eval (trace R) t r pub =
      Fp.ofNat ((vsAt R.segs r).cell c) := fun c => cell_eval R hg hr pub c
  generalize vsAt R.segs r = X at hx hcur ec0 ⊢
  have ev : ∀ (e : Expr) (v : Nat), zev (tenv (trace R) t r pub) e = (v : Int) →
      e.eval (trace R) t r pub = Fp.ofNat v := fun e v h => eval_ofNat h
  have ec := ec0
  simp only [Mem.interactions, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [multNat_one _ _ _ _ _ _ _ _ (ec Mem.act) (by simpa [MV.cell, Mem.act] using hx.bact),
    multNat_one _ _ _ _ _ _ _ _ (ec Mem.lst) (by simpa [MV.cell, Mem.lst] using hx.blst),
    multNat_one _ _ _ _ _ _ _ _ (ev _ (X.isRd + X.isGr) (by simp [hcur, MV.cell, Mem.isRd, Mem.isGr]))
      (by have := hx.kind; have := hx.bact; omega),
    multNat_one _ _ _ _ _ _ _ _ (ec Mem.isGr) (by simpa [MV.cell, Mem.isGr] using hx.bgr)]
  have hopE : Mem.opE.eval (trace R) t r pub = Fp.ofNat (X.isRd + 2 * X.isGr) :=
    ev _ _ (by simp [Mem.opE, hcur, MV.cell, Mem.isRd, Mem.isGr])
  have htp1 : (Expr.add (ZkFormal.Chacha.Table.E.c Mem.tp) (ZkFormal.Chacha.Table.E.k 1)).eval
      (trace R) t r pub = Fp.ofNat (X.tp + 1) := ev _ _ (by simp [hcur, MV.cell, Mem.tp])
  have hk1 : (ZkFormal.Chacha.Table.E.k 1).eval (trace R) t r pub = Fp.ofNat 1 := ev _ _ (by simp)
  simp only [Interaction.msgVal, List.map_cons, List.map_nil, ec, hopE, htp1, hk1]
  have e1 : [Fp.ofNat (X.cell Mem.addr), Fp.ofNat (X.cell Mem.t), Fp.ofNat (X.isRd + 2 * X.isGr),
      Fp.ofNat (X.cell Mem.vin), Fp.ofNat (X.cell Mem.v), Fp.ofNat (X.cell Mem.inc), Fp.ofNat (X.cell Mem.ok),
      Fp.ofNat (X.cell Mem.cc)] = (sopMsg X).map Fp.ofNat := by
    simp [sopMsg, MV.cell, Mem.addr, Mem.t, Mem.vin, Mem.v, Mem.inc, Mem.ok, Mem.cc]
  have e2 : [Fp.ofNat (X.cell Mem.addr), Fp.ofNat (X.cell Mem.v), Fp.ofNat (X.cell Mem.w)] =
      (finMsg X).map Fp.ofNat := by simp [finMsg, MV.cell, Mem.addr, Mem.v, Mem.w]
  have e3 : [Fp.ofNat (X.cell Mem.t), Fp.ofNat (X.tp + 1), Fp.ofNat 1] = (cmpTMsg X).map Fp.ofNat := by
    simp [cmpTMsg, MV.cell, Mem.t]
  have e4 : [Fp.ofNat (X.cell Mem.vin), Fp.ofNat (X.cell Mem.inc), Fp.ofNat (X.cell Mem.sf)] =
      (cmpVMsg X).map Fp.ofNat := by simp [cmpVMsg, MV.cell, Mem.vin, Mem.inc, Mem.sf]
  rw [e1, e2, e3, e4]
  rw [term_eq _ _ (by simpa [MV.cell, Mem.act] using hx.bact),
    term_eq _ _ (by simpa [MV.cell, Mem.lst] using hx.blst),
    term_eq _ _ (by have := hx.kind; have := hx.bact; omega),
    term_eq _ _ (by simpa [MV.cell, Mem.isGr] using hx.bgr)]
  unfold rowMsgs
  simp only [fmsgs_append, List.count_append]
  have h1 : ∀ (A : Prop) [Decidable A] (x : List Nat), fmsgs (if A then [x] else []) =
      if A then [x.map Fp.ofNat] else [] := fun A _ x => by split <;> rfl
  simp only [h1, MV.cell, Mem.act, Mem.lst, Mem.isGr]
  simp only [eq_comm (a := B_SOP), eq_comm (a := B_SFIN), eq_comm (a := B_SCMP), eq_comm (a := false),
    eq_comm (a := true)]
  simp
  omega

theorem mem_traffic (R : Run) (hg : ∀ g ∈ R.segs, SegOk g) (hrows : (memVs R.segs).length + 1 ≤ 2^22) (t : Nat) (pub : List Fp) (b : Nat)
    (send : Bool) (m : List Fp) :
    tableBusCount Mem.interactions (trace R) t pub b send m =
      (fmsgs ((memVs R.segs).flatMap (rowMsgs b send))).count m := by
  rw [busCount_sum]
  rw [List.map_congr_left (fun r hr => mem_row_count R hg t r pub (List.mem_range.1 hr) b send m)]
  have hlen : (memVs R.segs).length + 1 ≤ (trace R).height t := hrows
  rw [sum_range_trunc (fun r => (fmsgs (rowMsgs b send (vsAt R.segs r))).count m)
      (len := (memVs R.segs).length) (fun r hr => by
        rw [vsAt_ge hr]; unfold rowMsgs; simp [padV, fmsgs]) _ (by omega)]
  calc ((List.range (memVs R.segs).length).map
        (fun r => (fmsgs (rowMsgs b send (vsAt R.segs r))).count m)).sum
      = ((memVs R.segs).map fun V => (fmsgs (rowMsgs b send V)).count m).sum := by
        rw [← range_map_getD (memVs R.segs) padV]; rfl
    _ = _ := by
        rw [sum_count_flatMap']
        unfold fmsgs
        rw [List.map_flatMap]

end ZkFormal.NearV3.Candidates.MemHeight
