import ZkFormal.NearV3.Extract.Ups.LayoutMain
import ZkFormal.NearV3.Extract.Ups.Nev
import ZkFormal.NearV3.Extract.Ups.ByteRows
import ZkFormal.NearV3.Extract.Ups.PlanRows

/-!
# ZkFormal.NearV3.Extract.Ups.FieldBytes — byte lists of fields (layer 2)

`rowsB s r0 n`: the bytes `b` of rows `r0 … r0+n−1`.  A part's bytes are the concatenation of
its fields' bytes (`partBytes_fields`).  Field-level byte facts:

* a **fresh window** (`VH` not copied, or `CH` with `wfr`): its 32 bytes are the register of
  its first row, which receives `DIGEST (dI, dL, reg)` there (`freshWin`);
* a **fresh value length** (`VLEN` not copied): its 4 bytes are `L0 L1 L2 0` (`freshVlen`);
* the **tag** byte and the **hex-prefix length** `u32 qhk` (`tagByte`, `hplBytes`).
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- The bytes of rows `r0 … r0+n−1`. -/
def rowsB (s : UpsSeg) (r0 n : Nat) : List Nat := (List.range n).map fun d => s.row (r0 + d) b

/-- A column over rows `r0 … r0+n−1`. -/
def rowsC (s : UpsSeg) (x r0 n : Nat) : List Nat := (List.range n).map fun d => s.row (r0 + d) x

theorem rowsB_append (s : UpsSeg) (r0 n m : Nat) : rowsB s r0 (n + m) = rowsB s r0 n ++ rowsB s (r0 + n) m := by
  simp only [rowsB, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left; intro d _; simp [Function.comp, Nat.add_assoc]

/-- Consecutive pieces: the rows of `segEnd` are the concatenation of the pieces' rows. -/
theorem rowsB_consec (s : UpsSeg) (o : Nat) : ∀ (fl : List (Nat × Nat)) (s0 : Nat), Consec s0 fl →
    rowsB s (o + s0) (segEnd s0 fl - s0) = fl.flatMap (fun p => rowsB s (o + p.1) p.2)
  | [], s0, _ => by simp [segEnd, rowsB]
  | (s', ℓ) :: rest, s0, ⟨h1, h2⟩ => by
    subst h1
    have ih := rowsB_consec s o rest (s' + ℓ) h2
    have hle := segEnd_ge rest (s' + ℓ) h2
    simp only [segEnd, List.flatMap_cons]
    rw [show segEnd (s' + ℓ) rest - s' = ℓ + (segEnd (s' + ℓ) rest - (s' + ℓ)) by omega, rowsB_append, ← ih,
      Nat.add_assoc]

/-- **A part's bytes are its fields' bytes.** -/
theorem partBytes_fields {s : UpsSeg} {o ℓ : Nat} {fl : List (Nat × Nat)} {w : Nat} (U : UPartL s o ℓ fl w) :
    rowsB s o ℓ = fl.flatMap (fun p => rowsB s (o + p.1) p.2) := by
  have := rowsB_consec s o fl 0 U.consec
  rw [U.cover, Nat.add_zero, Nat.sub_zero] at this
  exact this

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- A fresh-window row: the byte is register byte 0; inside the window the register shifts. -/
theorem winRow (hW : (C sVH = 1 ∧ C cp = 0 ∧ C sCH = 0) ∨ (C sCH = 1 ∧ C wfr = 1 ∧ C sVH = 0)) :
    C b = C (reg 0) ∧ (C fe = 0 → ∀ i, i < 31 → D (reg i) = C (reg (i + 1))) := by
  have hv : C sVH * (1 - C cp) + C sCH * C wfr = 1 := by
    rcases hW with ⟨a, b', c'⟩ | ⟨a, b', c'⟩ <;> simp [a, b', c']
  have f1 := factN ok hC hD (e := .mul winFr (sub (c b) (c (reg 0)))) (memBytes (by simp [cBytes]))
  simp only [winFr] at f1
  nev_simp at f1
  have a := fun x => hC x
  have d := fun x => hD x
  simp only [P_lit] at a d
  have := a b; have := a (reg 0)
  refine ⟨?_, fun hfe i hi => ?_⟩
  · rcases hW with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp [h1, h2, h3] at f1 <;> omega
  · have g := factN ok hC hD (e := Dsl.mul3 winFr (not (c fe)) (sub (n (reg i)) (c (reg (i + 1)))))
      (memBytes (by
        unfold cBytes; simp only [List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inr ⟨i, hi, rfl⟩)))
    simp only [winFr] at g
    nev_simp at g
    have := a (reg (i + 1)); have := d (reg i)
    rcases hW with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp [h1, h2, h3, hfe] at g <;> omega

/-- The fresh value-length row and the `L` register. -/
theorem vlenRow (hv : C sVLEN = 1) :
    (C cp = 0 → C b = C (LR 0)) ∧
    (C fs = 1 → C (LR 0) = C L0 ∧ C (LR 1) = C L1 ∧ C (LR 2) = C L2) ∧
    (C fe = 0 → D (LR 0) = C (LR 1) ∧ D (LR 1) = C (LR 2) ∧ D (LR 2) = 0) := by
  have a := fun x => hC x
  have d := fun x => hD x
  simp only [P_lit] at a d
  have := a b; have := a (LR 0); have := a (LR 1); have := a (LR 2); have := a L0; have := a L1; have := a L2
  have := d (LR 0); have := d (LR 1); have := d (LR 2)
  have hm : C sMEM = 0 := by
    have := stSum ok hC
    have := le1 (stBool ok hC (x := sMEM) (by simp [states]))
    have := le1 (stBool ok hC (x := sTAG) (by simp [states])); have := le1 (stBool ok hC (x := sHPL) (by simp [states]))
    have := le1 (stBool ok hC (x := sHPF) (by simp [states])); have := le1 (stBool ok hC (x := sKEY) (by simp [states]))
    have := le1 (stBool ok hC (x := sVH) (by simp [states])); have := le1 (stBool ok hC (x := sBM) (by simp [states]))
    have := le1 (stBool ok hC (x := sCH) (by simp [states]))
    have := le1 (rowBool ok hC (x := qb) (by simp [rowBools]))
    omega
  refine ⟨fun hcp => ?_, fun hfs => ?_, fun hfe => ?_⟩
  · have f := factN ok hC hD (e := mul3 (c sVLEN) (not (c cp)) (sub (c b) (c (LR 0)))) (memBytes (by simp [cBytes]))
    nev_simp at f; simp [hv, hcp] at f; omega
  · have g := fun i (hi : i < 3) => factN ok hC hD (e := Dsl.mul3 (.add (c sVLEN) (c sMEM)) (c fs) (sub (c (LR i)) (c (Lb i))))
      (memMem (by
        unfold cMem; simp only [List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩))))))))
    have g0 := g 0 (by omega); have g1 := g 1 (by omega); have g2 := g 2 (by omega)
    simp only [Lb, List.getD_cons_zero, List.getD_cons_succ] at g0 g1 g2
    nev_simp at g0 g1 g2
    simp [hv, hm, hfs] at g0 g1 g2
    omega
  · have g := fun i (hi : i < 2) => factN ok hC hD (e := Dsl.mul3 (.add (c sVLEN) (c sMEM)) (not (c fe))
        (sub (n (LR i)) (c (LR (i + 1))))) (memMem (by
        unfold cMem; simp only [List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩)))))))
    have g0 := g 0 (by omega); have g1 := g 1 (by omega)
    have g2 := factN ok hC hD (e := mul3 (.add (c sVLEN) (c sMEM)) (not (c fe)) (n (LR 2))) (memMem (by simp [cMem]))
    nev_simp at g0 g1 g2
    simp [hv, hm, hfe] at g0 g1 g2
    omega

/-- Tag and hex-prefix length bytes. -/
theorem gramRow (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) :
    (C sTAG = 1 → C pf = 1 → C b = C qtb1 + 2 * C qtb2 + 3 * C qte) ∧
    (C sHPL = 1 → C fs = 1 → C qha = C b) ∧ (C sHPL = 1 → C fs = 1 → C qhs = 1) := by
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a b; have := a qhk; have := a qtb1; have := a qtb2; have := a qte
  refine ⟨fun h hpf => ?_, fun h h' => ?_, fun h h' => ?_⟩
  · have f := factN ok hC hD (e := .mul (c sTAG) (sub (c b) tagE)) (memBytes (by simp [cBytes]))
    simp only [tagE] at f
    nev_simp at f; simp [h] at f
    have := partBoolN ok hC hpf (x := qtb1) (by decide); have := partBoolN ok hC hpf (x := qtb2) (by decide)
    have := partBoolN ok hC hpf (x := qte) (by decide)
    omega
  · exact natv (hC _) (hC _) (bHPL0 ok hC hoh h h')
  · exact natv (hC _) (by unfold P; omega) (by simpa only [cast1] using bHPLr ok hC hoh h h')

end

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

/-- **A fresh window field** (32 rows, each a fresh-window row): its bytes are the 32 register
bytes of its first row. -/
theorem freshWin {r0 : Nat} (hlt : r0 + 32 ≤ s.rows.length)
    (hW : ∀ d, d < 32 → (s.row (r0 + d) sVH = 1 ∧ s.row (r0 + d) cp = 0 ∧ s.row (r0 + d) sCH = 0) ∨
      (s.row (r0 + d) sCH = 1 ∧ s.row (r0 + d) wfr = 1 ∧ s.row (r0 + d) sVH = 0))
    (hfe : ∀ d, d < 31 → s.row (r0 + d) fe = 0) :
    rowsB s r0 32 = (List.range 32).map fun i => s.row r0 (reg i) := by
  have R := fun d (hd : d < 32) => winRow (okRow hw hs (i := r0 + d) (by omega)) (rowLt hw hs _) (nextLt hw hs _) (hW d hd)
  have sh : ∀ d, d < 32 → ∀ i, i + d < 32 → s.row (r0 + d) (reg i) = s.row r0 (reg (i + d)) := by
    intro d
    induction d with
    | zero => intro _ i _; rfl
    | succ d ih =>
      intro hd i hi
      have hn := (R d (by omega)).2 (hfe d (by omega)) i (by omega)
      rw [next_eq hw hs (by omega)] at hn
      rw [show r0 + (d + 1) = r0 + d + 1 by omega, hn, ih (by omega) (i + 1) (by omega)]
      congr 2; omega
  apply List.ext_getElem (by simp [rowsB])
  intro d h1 h2
  simp only [rowsB, List.getElem_map, List.getElem_range]
  simp only [rowsB, List.length_map, List.length_range] at h1
  rw [(R d h1).1, sh d h1 0 (by omega), Nat.zero_add]

/-- **A fresh value-length field** (4 rows, `VLEN`, not copied): `L0 L1 L2 0`. -/
theorem freshVlen {r0 : Nat} (hlt : r0 + 4 ≤ s.rows.length)
    (hV : ∀ d, d < 4 → s.row (r0 + d) sVLEN = 1 ∧ s.row (r0 + d) cp = 0)
    (hfs : s.row r0 fs = 1) (hfe : ∀ d, d < 3 → s.row (r0 + d) fe = 0) :
    rowsB s r0 4 = [s.row r0 L0, s.row r0 L1, s.row r0 L2, 0] := by
  have R := fun d (hd : d < 4) => vlenRow (okRow hw hs (i := r0 + d) (by omega)) (rowLt hw hs _) (nextLt hw hs _) (hV d hd).1
  have nx := fun d (hd : d < 3) => next_eq hw hs (i := r0 + d) (by omega)
  have i0 := (R 0 (by omega)).2.1 (by simpa using hfs)
  have s0 := (R 0 (by omega)).2.2 (hfe 0 (by omega))
  have s1 := (R 1 (by omega)).2.2 (hfe 1 (by omega))
  have s2 := (R 2 (by omega)).2.2 (hfe 2 (by omega))
  rw [nx 0 (by omega)] at s0; rw [nx 1 (by omega)] at s1; rw [nx 2 (by omega)] at s2
  have b0 := (R 0 (by omega)).1 (hV 0 (by omega)).2
  have b1 := (R 1 (by omega)).1 (hV 1 (by omega)).2
  have b2 := (R 2 (by omega)).1 (hV 2 (by omega)).2
  have b3 := (R 3 (by omega)).1 (hV 3 (by omega)).2
  simp only [Nat.add_zero] at i0 s0 b0
  simp only [rowsB, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, Nat.add_zero]
  rw [b0, b1, b2, b3]
  rw [show r0 + 0 + 1 = r0 + 1 from rfl] at s0
  rw [show r0 + 1 + 1 = r0 + 2 from rfl] at s1
  rw [show r0 + 2 + 1 = r0 + 3 from rfl] at s2
  rw [s1.1, s0.2.1, s0.1, i0.1, i0.2.1, i0.2.2, s2.1, s1.2.1, s0.2.2]

end

end ZkFormal.NearV3.UpsRows
