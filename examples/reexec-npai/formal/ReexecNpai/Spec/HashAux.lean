import ReexecNpai.Spec.State

/-!
# Auxiliary lemmas for the hash pass

* preimage layout: where the value-hash and child-hash placeholders sit
  inside `preImg` (`preImg_vh`, `preImg_slot`, `vh_lt_slot`, `slot_lt`);
* arena geometry: records are disjoint and increasing (`rec_order`), and
  every non-root entry is a revealed child of a later entry (`parent_of`).
-/

set_option maxRecDepth 8000

namespace ReexecNpai.HashAux

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-! ## Preimage layout -/

/-- Offset of the hash slot of the `q`-th revealed child inside the preimage. -/
def slotAt (nf : NF) (q : Nat) : Nat :=
  match nf with
  | .branch _ ks _ => slotOff nf + 32 * slotPos ks q
  | _ => slotOff nf

theorem childSlot_eq (e : Ent) (q : Nat) : childSlot e q = e.pre + slotAt e.nf q := by
  unfold childSlot slotAt
  cases e.nf <;> simp [Nat.add_assoc]

theorem preImg_vh {nf : NF} (hv : hasVal nf = true) (vlen : Nat) (zs : List Bytes) :
    ∃ X Y : Bytes, X.length = vhOff nf ∧ 0 < Y.length ∧ ∀ w, preImg nf vlen w zs = X ++ w ++ Y := by
  cases nf with
  | leaf k ref mm =>
    cases ref with
    | none =>
      exact ⟨[0] ++ u32 (hexPrefix k true).length ++ hexPrefix k true ++ u32 vlen, u64 mm,
        by simp [vhOff]; omega, by simp, fun w => by simp [preImg]⟩
    | some _ => simp [hasVal] at hv
  | ext k h mm => simp [hasVal] at hv
  | branch v ks mm =>
    rcases v with _ | _ | _
    · simp [hasVal] at hv
    · exact ⟨[2] ++ u32 vlen, u16 (bitsPres ks 0) ++ slotBytes ks zs ++ u64 mm, by simp [vhOff], by simp; omega,
        fun w => by simp [preImg]⟩
    · simp [hasVal] at hv

theorem preImg_novh {nf : NF} (hv : hasVal nf = false) (vlen : Nat) (z z' : Bytes) (zs : List Bytes) :
    preImg nf vlen z zs = preImg nf vlen z' zs := by
  cases nf with
  | leaf k ref mm =>
    cases ref with
    | none => simp [hasVal] at hv
    | some _ => simp [preImg]
  | ext k h mm => simp [preImg]
  | branch v ks mm =>
    rcases v with _ | _ | _
    · simp [preImg]
    · simp [hasVal] at hv
    · simp [preImg]

theorem nRev_cons_none (r : List (Option (Option Bytes))) : nRev (none :: r) = nRev r := by
  rw [nRev_cons]; simp
theorem nRev_cons_some (h : Bytes) (r : List (Option (Option Bytes))) : nRev (some (some h) :: r) = nRev r := by
  rw [nRev_cons]; simp
theorem nRev_cons_rev (r : List (Option (Option Bytes))) : nRev (some none :: r) = nRev r + 1 := by
  rw [nRev_cons]; simp

theorem slotBytes_set : ∀ (ks : List (Option (Option Bytes))),
    (∀ s ∈ ks, match s with | some (some h) => h.length = 32 | _ => True) →
    ∀ (zs : List Bytes) (q : Nat), zs.length = nRev ks → (∀ x ∈ zs, x.length = 32) → q < nRev ks →
    ∃ X Y : Bytes, X.length = 32 * slotPos ks q ∧ ∀ w, slotBytes ks (zs.set q w) = X ++ w ++ Y
  | [], _, _, q, _, _, hq => by simp at hq
  | none :: r, hks, zs, q, hl, h32, hq => by
    rw [nRev_cons_none] at hl hq
    obtain ⟨X, Y, hX, hw⟩ := slotBytes_set r (fun s hs => hks s (List.mem_cons_of_mem _ hs)) zs q hl h32 hq
    exact ⟨X, Y, by simpa [slotPos] using hX, fun w => by simpa [slotBytes] using hw w⟩
  | some (some h) :: r, hks, zs, q, hl, h32, hq => by
    rw [nRev_cons_some] at hl hq
    obtain ⟨X, Y, hX, hw⟩ := slotBytes_set r (fun s hs => hks s (List.mem_cons_of_mem _ hs)) zs q hl h32 hq
    have hh : h.length = 32 := hks _ List.mem_cons_self
    exact ⟨h ++ X, Y, by simp [slotPos, hX, hh]; omega, fun w => by simp [slotBytes, hw w]⟩
  | some none :: r, hks, zs, q, hl, h32, hq => by
    rw [nRev_cons_rev] at hl hq
    obtain _ | ⟨a, zs'⟩ := zs
    · simp at hl
    · simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      rcases q with _ | q
      · exact ⟨[], slotBytes r zs', by simp [slotPos], fun w => by simp [slotBytes]⟩
      · have ha : a.length = 32 := h32 a List.mem_cons_self
        obtain ⟨X, Y, hX, hw⟩ := slotBytes_set r (fun s hs => hks s (List.mem_cons_of_mem _ hs)) zs' q hl
          (fun x hx => h32 x (List.mem_cons_of_mem _ hx)) (by omega)
        exact ⟨a ++ X, Y, by simp [slotPos, hX, ha]; omega, fun w => by simp [slotBytes, hw w]⟩

theorem preImg_slot {nf : NF} (hok : NFOk nf) (vlen : Nat) {z : Bytes} (hz : z.length = 32) {zs : List Bytes}
    (hzs : zs.length = nKids nf) (h32 : ∀ x ∈ zs, x.length = 32) {q : Nat} (hq : q < nKids nf) :
    ∃ X Y : Bytes, X.length = slotAt nf q ∧ 0 < Y.length ∧ ∀ w, preImg nf vlen z (zs.set q w) = X ++ w ++ Y := by
  cases nf with
  | leaf k ref mm => simp [nKids] at hq
  | ext k h mm =>
    cases h with
    | some _ => simp [nKids] at hq
    | none =>
      simp only [nKids, Option.isNone_none, ↓reduceIte] at hq hzs
      obtain _ | ⟨a, _ | ⟨b, zs'⟩⟩ := zs
      · simp at hzs
      · have : q = 0 := by omega
        subst this
        exact ⟨[3] ++ u32 (hexPrefix k false).length ++ hexPrefix k false, u64 mm, by simp [slotAt, slotOff]; omega,
          by simp, fun w => by simp [preImg]⟩
      · simp at hzs
  | branch v ks mm =>
    obtain ⟨-, -, hv, hks⟩ := hok
    simp only [nKids] at hq hzs
    obtain ⟨X, Y, hX, hw⟩ := slotBytes_set ks hks zs q hzs h32 hq
    rcases v with _ | _ | ⟨len, h⟩
    · exact ⟨[1] ++ u16 (bitsPres ks 0) ++ X, Y ++ u64 mm, by simp [slotAt, slotOff, hX]; omega, by simp,
        fun w => by simp [preImg, hw w]⟩
    · exact ⟨[2] ++ u32 vlen ++ z ++ u16 (bitsPres ks 0) ++ X, Y ++ u64 mm,
        by simp [slotAt, slotOff, hX, hz]; omega, by simp, fun w => by simp [preImg, hw w]⟩
    · simp only at hv
      exact ⟨[2] ++ u32 len ++ h ++ u16 (bitsPres ks 0) ++ X, Y ++ u64 mm,
        by simp [slotAt, slotOff, hX, hv.2]; omega, by simp, fun w => by simp [preImg, hw w]⟩

theorem vh_lt_slot {nf : NF} (hv : hasVal nf = true) {q : Nat} (hq : q < nKids nf) :
    vhOff nf + 32 ≤ slotAt nf q := by
  cases nf with
  | leaf k ref mm => simp [nKids] at hq
  | ext k h mm => simp [hasVal] at hv
  | branch v ks mm =>
    rcases v with _ | _ | _
    · simp [hasVal] at hv
    · simp [vhOff, slotAt, slotOff]; omega
    · simp [hasVal] at hv

theorem slotPos_lt : ∀ (ks : List (Option (Option Bytes))) (q q' : Nat), q < q' → q' < nRev ks →
    slotPos ks q < slotPos ks q'
  | [], _, _, _, h => by simp at h
  | none :: r, q, q', h, h' => by
    rw [nRev_cons_none] at h'; simpa [slotPos] using slotPos_lt r q q' h h'
  | some (some _) :: r, q, q', h, h' => by
    rw [nRev_cons_some] at h'; have := slotPos_lt r q q' h h'; simp [slotPos]; omega
  | some none :: r, q, q', h, h' => by
    rw [nRev_cons_rev] at h'
    rcases q with _ | q <;> rcases q' with _ | q'
    · omega
    · simp [slotPos]; omega
    · omega
    · have := slotPos_lt r q q' (by omega) (by omega); simp [slotPos]; omega

theorem slot_lt {nf : NF} {q q' : Nat} (h : q < q') (h' : q' < nKids nf) : slotAt nf q + 32 ≤ slotAt nf q' := by
  cases nf with
  | leaf k ref mm => simp [nKids] at h'
  | ext k hh mm =>
    simp only [nKids] at h'
    split at h' <;> omega
  | branch v ks mm =>
    have := slotPos_lt ks q q' h (by simpa [nKids] using h')
    simp only [slotAt]; omega

theorem preImg_len (nf : NF) (vlen : Nat) (z : Bytes) (zs : List Bytes) : 9 ≤ (preImg nf vlen z zs).length := by
  cases nf with
  | leaf k ref mm => simp [preImg]; omega
  | ext k h mm => simp [preImg]; omega
  | branch v ks mm => simp [preImg]; omega

/-! ## Arena geometry -/

section
variable {pb : Bytes} {A : List Ent} {K : List Nat} {start : Nat}

theorem getD_eq_get {j : Nat} (h : j < A.length) : A.getD j default = A[j] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem lt_of_get? {j : Nat} {e : Ent} (h : A[j]? = some e) : j < A.length := by
  rcases Nat.lt_or_ge j A.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none h'] at h; cases h

theorem get_of_get? {j : Nat} {e : Ent} (h : A[j]? = some e) : A[j]'(lt_of_get? h) = e := by
  rw [List.getElem?_eq_getElem (lt_of_get? h)] at h; exact Option.some.inj h

/-- Per-entry facts from `NodeWF`. -/
theorem ent_facts (hw : ArenaWF pb A K start) {j : Nat} (hj : j < A.length) :
    NFOk A[j].nf ∧ PF ≤ A[j].rst ∧ A[j].rst < A[j].pre ∧ A[j].pre + A[j].preLen ≤ PF + pb.length ∧
    (hasVal A[j].nf = true → A[j].val = A[j].rst + 5 ∧ vlenAt pb A[j] < 4294967296 ∧
      A[j].val + vlenAt pb A[j] ≤ A[j].pre) ∧
    (hasVal A[j].nf = false → A[j].val = 0) := by
  obtain ⟨e, he, hok, h1, h2, h3, -, hv, -⟩ := hw.nodes j hj
  rw [List.getElem?_eq_getElem hj] at he
  cases he
  refine ⟨hok, h1, h2, h3, fun h => ?_, fun h => ?_⟩
  · simp only [h, ↓reduceIte] at hv; omega
  · simpa [h] using hv

theorem rec_order (hw : ArenaWF pb A K start) : ∀ {y : Nat} (hy : y < A.length) {x : Nat} (hx : x < y),
    A[x].pre + A[x].preLen ≤ A[y].rst
  | 0, _, _, hx => by omega
  | y + 1, hy, x, hx => by
    have hc := hw.contig y hy
    rw [getD_eq_get (by omega), getD_eq_get hy] at hc
    rcases Nat.lt_or_ge x y with h | h
    · have := rec_order hw (y := y) (by omega) h
      have := (ent_facts hw (j := y) (by omega)).2.2.1
      omega
    · have : x = y := by omega
      subst this; omega

theorem start_le (hw : ArenaWF pb A K start) {x : Nat} (hx : x < A.length) : start ≤ A[x].rst := by
  have h0 := hw.first
  rw [getD_eq_get (by omega)] at h0
  rcases x with _ | x
  · omega
  · have := rec_order hw hx (x := 0) (by omega)
    have := (ent_facts hw (j := 0) (by omega)).2.2.1
    omega

theorem end_le (hw : ArenaWF pb A K start) {x : Nat} (hx : x < A.length) :
    A[x].pre + A[x].preLen ≤ PF + pb.length := (ent_facts hw hx).2.2.2.1

/-- Two 32-byte regions inside the preimages of different entries are disjoint. -/
theorem recs_disj (hw : ArenaWF pb A K start) {x y : Nat} (hx : x < A.length) (hy : y < A.length) (hxy : x ≠ y)
    {a b n : Nat} (ha1 : A[x].pre ≤ a) (ha2 : a + n ≤ A[x].pre + A[x].preLen)
    (hb1 : A[y].pre ≤ b) (hb2 : b + n ≤ A[y].pre + A[y].preLen) : a + n ≤ b ∨ b + n ≤ a := by
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · have := rec_order hw hy h; have := (ent_facts hw hy).2.2.1; omega
  · have := rec_order hw hx h; have := (ent_facts hw hx).2.2.1; omega

/-- The revealed children of `e` cover `[e.lo, c)`. -/
theorem cover (hw : ArenaWF pb A K start) {c : Nat} {e : Ent} (hc : A[c]? = some e) {x : Nat}
    (h1 : e.lo ≤ x) (h2 : x < c) :
    ∃ q, q < nKids e.nf ∧ ∃ ec, A[childIdx K e.kid (nKids e.nf) q]? = some ec ∧ ec.lo ≤ x ∧
      x ≤ childIdx K e.kid (nKids e.nf) q := by
  obtain ⟨-, h0, hch, -⟩ := nodeWF_of hw hc
  have key : ∀ q, q < nKids e.nf → x ≤ childIdx K e.kid (nKids e.nf) q →
      ∃ q', q' < nKids e.nf ∧ ∃ ec, A[childIdx K e.kid (nKids e.nf) q']? = some ec ∧ ec.lo ≤ x ∧
        x ≤ childIdx K e.kid (nKids e.nf) q' := by
    intro q
    induction q with
    | zero =>
      intro hq hx
      obtain ⟨ec, hec, -, hlo, -⟩ := hch 0 hq
      simp only [↓reduceIte] at hlo
      exact ⟨0, hq, ec, hec, by omega, hx⟩
    | succ q ih =>
      intro hq hx
      by_cases hx' : x ≤ childIdx K e.kid (nKids e.nf) q
      · exact ih (by omega) hx'
      · obtain ⟨ec, hec, -, hlo, -⟩ := hch (q + 1) hq
        simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hlo
        exact ⟨q + 1, hq, ec, hec, by omega, hx⟩
  have hn : nKids e.nf ≠ 0 := fun h => by have := h0 h; omega
  obtain ⟨-, -, -, -, hl⟩ := hch (nKids e.nf - 1) (by omega)
  have := hl (by omega)
  exact key (nKids e.nf - 1) (by omega) (by omega)

theorem parent_aux (hw : ArenaWF pb A K start) (c : Nat) : ∀ {e : Ent}, A[c]? = some e → ∀ x, e.lo ≤ x → x < c →
    ∃ p ep q, A[p]? = some ep ∧ q < nKids ep.nf ∧ x < p ∧ childIdx K ep.kid (nKids ep.nf) q = x := by
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro e hc x h1 h2
    obtain ⟨q, hq, ec, hec, hlo, hle⟩ := cover hw hc h1 h2
    rcases Nat.lt_or_ge x (childIdx K e.kid (nKids e.nf) q) with h | h
    · obtain ⟨-, hlt, -⟩ := child_info hw hc hq
      exact ih _ (by
        obtain ⟨ec', hec', hlt', -⟩ := child_info hw hc hq
        exact hlt') hec x hlo h
    · exact ⟨c, e, q, hc, hq, h2, by omega⟩

/-- Every non-root entry is the `q`-th revealed child of a later entry `p`, and its hash slot is
the corresponding slot of `p`'s preimage. -/
theorem parent_of (hw : ArenaWF pb A K start) {x : Nat} (hx : x + 1 < A.length) :
    ∃ p q, ∃ hp : p < A.length, q < nKids A[p].nf ∧ x < p ∧ childIdx K A[p].kid (nKids A[p].nf) q = x ∧
      A[x].pslot = childSlot A[p] q := by
  have hr := hw.root_lo
  rw [getD_eq_get (by omega)] at hr
  obtain ⟨p, ep, q, hp, hq, hxp, hc⟩ := parent_aux hw (A.length - 1)
    (List.getElem?_eq_getElem (by omega)) x (by omega) (by omega)
  have hpl := lt_of_get? hp
  have hep := get_of_get? hp
  rw [← hep] at hq hc
  refine ⟨p, q, hpl, hq, hxp, hc, ?_⟩
  obtain ⟨e', he', -, -, -, -, -, -, -, -, -, h3, -⟩ := hw.nodes p hpl
  rw [List.getElem?_eq_getElem hpl] at he'
  cases he'
  obtain ⟨ec, hec, -, hps, -⟩ := h3 q hq
  rw [hc] at hec
  rw [get_of_get? hec]
  exact hps

end


/-! ## Byte helpers -/

theorem read_split {M0 : Nat → UInt8} {a n : Nat} {X v Y : Bytes} (h : readMem M0 a n = X ++ v ++ Y) :
    n = X.length + v.length + Y.length ∧ readMem M0 a X.length = X ∧
      readMem M0 (a + X.length) v.length = v ∧ readMem M0 (a + X.length + v.length) Y.length = Y := by
  have hn : n = X.length + v.length + Y.length := by
    have := congrArg List.length h; simp at this; omega
  subst hn
  rw [readMem_add, readMem_add] at h
  obtain ⟨h12, h3⟩ := List.append_inj h (by simp)
  obtain ⟨h1, h2⟩ := List.append_inj h12 (by simp)
  exact ⟨rfl, h1, h2, by rw [Nat.add_assoc]; exact h3⟩

theorem read_mid {M0 : Nat → UInt8} {a n : Nat} {X v Y : Bytes} (h : readMem M0 a n = X ++ v ++ Y) :
    readMem M0 (a + X.length) v.length = v := (read_split h).2.2.1

theorem write_mid {M0 : Nat → UInt8} {a n : Nat} {X v Y w : Bytes} (h : readMem M0 a n = X ++ v ++ Y)
    (hw : w.length = v.length) :
    readMem (writeMem M0 (a + X.length) w.length w) a n = X ++ w ++ Y := by
  obtain ⟨hn, h1, -, h3⟩ := read_split h
  subst hn
  have e1 : readMem (writeMem M0 (a + X.length) w.length w) a X.length = X := by
    rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega), h1]
  have e3 : readMem (writeMem M0 (a + X.length) w.length w) (a + X.length + v.length) Y.length = Y := by
    rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega), h3]
  have e2 : readMem (writeMem M0 (a + X.length) w.length w) (a + X.length) v.length = w := by
    rw [← hw, readMem_writeMem_self _ _ _ _ (Nat.le_refl _), List.take_length]
  rw [readMem_add, readMem_add, e1, e2, ← Nat.add_assoc, e3]

theorem read_write_self (M0 : Nat → UInt8) (d : Nat) (w : Bytes) (hw : w.length = 32) :
    readMem (writeMem M0 d 32 w) d 32 = w := by
  rw [readMem_writeMem_self _ _ _ _ (by omega), ← hw, List.take_length]

/-! ## Frames for `TrieSt` -/

section
variable {cb pb : Bytes} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes}

theorem trieSt_regs {m m' : M} (h : TrieSt cb pb rs R A K vals m) (hm : m'.mem = m.mem)
    (h14 : m'.regs 14 = 8) (h15 : m'.regs 15 = 1) : TrieSt cb pb rs R A K vals m' := by
  obtain ⟨r', mem'⟩ := m'
  simp only at hm h14 h15
  subst hm
  exact ⟨⟨⟨⟨h15, h14, h.data⟩, h.claim, h.toClaimIn.3⟩, h.ok, h.rcpts, h.plen, h.pend, h.nC, h.rend, h.rt⟩,
    h.tok, ⟨h.tmem.amem, h.tmem.kmem, h.tmem.krange, h.tmem.klen, h.tmem.nodes, h.tmem.vmem, h.tmem.lmem,
      h.tmem.pmem, h.tmem.hmem⟩⟩

/-- Generic frame: a write that preserves every region `TrieSt` observes, except possibly
preimage contents, for which a new witness is supplied. -/
theorem trieSt_frame {m : M} (h : TrieSt cb pb rs R A K vals m) (M' : Nat → UInt8)
    (hlow : ∀ a k, a + k ≤ 3136 ∨ (3168 ≤ a ∧ a + k ≤ PF + R + 4) → readMem M' a k = readMem m.mem a k)
    (hv : ∀ j (hj : j < A.length), ∀ a k, A[j].rst ≤ a + 1 → a + k ≤ A[j].pre → readMem M' a k = readMem m.mem a k)
    (hp : ∀ j (hj : j < A.length), ∃ z zs, z.length = 32 ∧ zs.length = nKids A[j].nf ∧
      (∀ x ∈ zs, x.length = 32) ∧ readMem M' A[j].pre A[j].preLen = preImg A[j].nf (vlenAt pb A[j]) z zs) :
    TrieSt cb pb rs R A K vals ⟨m.regs, M'⟩ := by
  have hw := h.tok.wf
  have hK := h.tmem.klen
  have hN := hw.len_le
  have hrs := h.ok.n_max
  have hR := h.ok.Rle
  simp only [NCAP, Params.maxBatch] at hK hN hrs
  have r4 : ∀ a, a + 4 ≤ 3136 ∨ (3168 ≤ a ∧ a + 4 ≤ PF + R + 4) → rd32 ⟨m.regs, M'⟩ a = rd32 m a := by
    intro a ha; simp only [rd32]; rw [hlow a 4 ha]
  refine ⟨⟨⟨⟨h.k1, h.k8, ?_⟩, ?_, h.toClaimIn.3⟩, h.ok, ?_, h.plen, ?_, ?_, ?_, ?_⟩, h.tok,
    ⟨?_, ?_, h.tmem.krange, h.tmem.klen, ?_, ?_, ?_, hp, ?_⟩⟩
  · rw [hlow _ _ (by omega)]; exact h.data
  · rw [hlow _ _ (by simp [CLM])]; exact h.claim
  · rw [hlow _ _ (by simp [PF])]; exact h.rcpts
  · rw [r4 _ (by simp [C_PEND])]; exact h.pend
  · rw [r4 _ (by simp [C_N])]; exact h.nC
  · rw [r4 _ (by simp [C_REND])]; exact h.rend
  · intro i hi; rw [hlow _ _ (by simp [RT, PF]; omega)]; exact h.rt i hi
  · intro j hj
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.tmem.amem j hj
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (rw [r4 _ (by simp [AR, PF]; omega)]; assumption)
  · intro i hi; rw [r4 _ (by simp [KL, PF]; omega)]; exact h.tmem.kmem i hi
  · rw [r4 _ (by simp [C_NODES])]; exact h.tmem.nodes
  · intro j hj hj'
    obtain ⟨-, -, -, -, hv', -⟩ := ent_facts hw hj
    obtain ⟨e1, e2, e3⟩ := hv' hj'
    rw [hv j hj _ _ (by omega) (by omega)]; exact h.tmem.vmem j hj hj'
  · intro j hj hj'
    obtain ⟨-, -, -, -, hv', -⟩ := ent_facts hw hj
    obtain ⟨e1, e2, e3⟩ := hv' hj'
    rw [hv j hj _ _ (by omega) (by omega)]; exact h.tmem.lmem j hj hj'
  · intro j hj
    have h0 := h.tmem.hmem j hj
    obtain ⟨-, hpf, hlt, -⟩ := ent_facts hw hj
    simp only [PF] at hpf
    revert h0
    cases A[j].nf with
    | leaf => intro _; trivial
    | ext => intro h0; simp only at h0 ⊢; rw [hv j hj _ _ (by omega) (by omega)]; exact h0
    | branch => intro h0; simp only at h0 ⊢; rw [hv j hj _ _ (by omega) (by omega)]; exact h0

theorem trieSt_write_in {m : M} (h : TrieSt cb pb rs R A K vals m) {p d n : Nat} {w : Bytes}
    (hp : p < A.length) (hd1 : A[p].pre ≤ d) (hd2 : d + n < A[p].pre + A[p].preLen)
    (hpm : ∃ z zs, z.length = 32 ∧ zs.length = nKids A[p].nf ∧ (∀ x ∈ zs, x.length = 32) ∧
      readMem (writeMem m.mem d n w) A[p].pre A[p].preLen = preImg A[p].nf (vlenAt pb A[p]) z zs) :
    TrieSt cb pb rs R A K vals ⟨m.regs, writeMem m.mem d n w⟩ := by
  have hw := h.tok.wf
  have hs := start_le hw hp
  have hp1 := (ent_facts hw hp).2.2.1
  apply trieSt_frame h
  · intro a k hak
    simp only [PF] at hak hs
    exact readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)
  · intro j hj a k h1 h2
    apply readMem_writeMem_disjoint
    rcases Nat.lt_trichotomy j p with hjp | hjp | hjp
    · have := rec_order hw hp hjp; have := (ent_facts hw hj).2.2.1; omega
    · subst hjp; omega
    · have := rec_order hw hj hjp; omega
  · intro j hj
    by_cases hjp : j = p
    · subst hjp; exact hpm
    · obtain ⟨z, zs, a1, a2, a3, a4⟩ := h.tmem.pmem j hj
      refine ⟨z, zs, a1, a2, a3, ?_⟩
      rw [readMem_writeMem_disjoint _ _ _ _ _ _ ?_, a4]
      rcases Nat.lt_or_gt_of_ne hjp with hjp | hjp
      · have := rec_order hw hp hjp; omega
      · have := rec_order hw hj hjp; have := (ent_facts hw hj).2.2.1; omega

theorem trieSt_write_root {m : M} (h : TrieSt cb pb rs R A K vals m) (w : Bytes) :
    TrieSt cb pb rs R A K vals ⟨m.regs, writeMem m.mem C_ROOT 32 w⟩ := by
  have hw := h.tok.wf
  apply trieSt_frame h
  · intro a k hak
    exact readMem_writeMem_disjoint _ _ _ _ _ _ (by simp only [C_ROOT]; omega)
  · intro j hj a k h1 h2
    have := (ent_facts hw hj).2.1
    simp only [PF] at this
    exact readMem_writeMem_disjoint _ _ _ _ _ _ (by simp only [C_ROOT]; omega)
  · intro j hj
    obtain ⟨z, zs, a1, a2, a3, a4⟩ := h.tmem.pmem j hj
    refine ⟨z, zs, a1, a2, a3, ?_⟩
    have := (ent_facts hw hj).2
    simp only [PF] at this
    rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by simp only [C_ROOT]; omega), a4]

theorem child_slot (hw : ArenaWF pb A K start) {j q : Nat} (hj : j < A.length) (hq : q < nKids A[j].nf) :
    ∃ hc : childIdx K A[j].kid (nKids A[j].nf) q < A.length, childIdx K A[j].kid (nKids A[j].nf) q < j ∧
      A[childIdx K A[j].kid (nKids A[j].nf) q].pslot = childSlot A[j] q := by
  obtain ⟨e', he', -, -, -, -, -, -, -, -, -, h3, -⟩ := hw.nodes j hj
  rw [List.getElem?_eq_getElem hj] at he'
  cases he'
  obtain ⟨ec, hec, hlt, hps, -⟩ := h3 q hq
  have hc := lt_of_get? hec
  refine ⟨hc, hlt, ?_⟩
  rw [get_of_get? hec]; exact hps

theorem slot_in {m : M} (h : TrieSt cb pb rs R A K vals m) {p q : Nat} (hp : p < A.length)
    (hq : q < nKids A[p].nf) : slotAt A[p].nf q + 32 < A[p].preLen := by
  obtain ⟨z, zs, a1, a2, a3, a4⟩ := h.tmem.pmem p hp
  obtain ⟨X, Y, hX, hY, hs⟩ := preImg_slot (ent_facts h.tok.wf hp).1 (vlenAt pb A[p]) a1 a2 a3 hq
  have hql : q < zs.length := by omega
  have e := hs (zs[q]'hql)
  rw [List.set_getElem_self] at e
  have := (read_split (a4.trans e)).1
  have := a3 _ (List.getElem_mem hql)
  omega

theorem vh_in {m : M} (h : TrieSt cb pb rs R A K vals m) {p : Nat} (hp : p < A.length)
    (hv : hasVal A[p].nf = true) : vhOff A[p].nf + 32 < A[p].preLen := by
  obtain ⟨z, zs, a1, a2, a3, a4⟩ := h.tmem.pmem p hp
  obtain ⟨X, Y, hX, hY, hs⟩ := preImg_vh hv (vlenAt pb A[p]) zs
  have := (read_split (a4.trans (hs z))).1
  omega

/-- Hash slots of the processed non-root entries hold their hashes. -/
def SlotInv (A : List Ent) (K : List Nat) (vals : Nat → Bytes) (j : Nat) (M0 : Nat → UInt8) : Prop :=
  ∀ x (hx : x < A.length), x < j → x + 1 < A.length → readMem M0 A[x].pslot 32 = (treeAt A K vals x).hashOf

theorem hashOf_length (hw : ArenaWF pb A K start) (hvm : ∀ j (h : j < A.length), hasVal A[j].nf = true →
    (vals j).length = vlenAt pb A[j]) {x : Nat} (hx : x < A.length) :
    (treeAt A K vals x).hashOf.length = 32 := by
  rw [hashOf_treeAt hw (List.getElem?_eq_getElem hx) (hvm x hx)]; exact ArenaCore.sha256_length _

theorem childHashes_len (hw : ArenaWF pb A K start) (hvm : ∀ j (h : j < A.length), hasVal A[j].nf = true →
    (vals j).length = vlenAt pb A[j]) {j : Nat} (hj : j < A.length) :
    (childHashes A K vals A[j]).length = nKids A[j].nf ∧ ∀ x ∈ childHashes A K vals A[j], x.length = 32 := by
  refine ⟨by simp [childHashes], ?_⟩
  intro x hx
  simp only [childHashes, List.mem_map, List.mem_range] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  obtain ⟨hc, -, -⟩ := child_slot hw hj hq
  exact hashOf_length hw hvm hc

theorem children_eq {m : M} (h : TrieSt cb pb rs R A K vals m) {j : Nat} (hj : j < A.length)
    (hs : SlotInv A K vals j m.mem) :
    ∃ z : Bytes, z.length = 32 ∧
      readMem m.mem A[j].pre A[j].preLen = preImg A[j].nf (vlenAt pb A[j]) z (childHashes A K vals A[j]) := by
  have hw := h.tok.wf
  obtain ⟨z, zs, a1, a2, a3, a4⟩ := h.tmem.pmem j hj
  refine ⟨z, a1, ?_⟩
  rw [a4]
  congr 1
  apply List.ext_getElem (by simp [childHashes, a2])
  intro q h1 h2
  have hq : q < nKids A[j].nf := by omega
  obtain ⟨X, Y, hX, hY, hset⟩ := preImg_slot (ent_facts hw hj).1 (vlenAt pb A[j]) a1 a2 a3 hq
  have e := hset zs[q]
  rw [List.set_getElem_self] at e
  have r := read_mid (a4.trans e)
  obtain ⟨hc, hlt, hps⟩ := child_slot hw hj hq
  have := hs _ hc hlt (by omega)
  rw [hps, childSlot_eq, ← hX] at this
  rw [a3 _ (List.getElem_mem h1)] at r
  rw [← r, this]
  simp [childHashes]

theorem mid_val {m : M} (h : TrieSt cb pb rs R A K vals m) {j : Nat} (hj : j < A.length)
    (hs : SlotInv A K vals j m.mem) (hv : hasVal A[j].nf = true) :
    TrieSt cb pb rs R A K vals ⟨m.regs, writeMem m.mem (A[j].pre + vhOff A[j].nf) 32 (sha256 (vals j))⟩ ∧
    SlotInv A K vals j (writeMem m.mem (A[j].pre + vhOff A[j].nf) 32 (sha256 (vals j))) ∧
    readMem (writeMem m.mem (A[j].pre + vhOff A[j].nf) 32 (sha256 (vals j))) A[j].pre A[j].preLen =
      preImg A[j].nf (vlenAt pb A[j]) (sha256 (vals j)) (childHashes A K vals A[j]) := by
  have hw := h.tok.wf
  have hvm : ∀ j (h : j < A.length), hasVal A[j].nf = true → (vals j).length = vlenAt pb A[j] :=
    fun j hj hv => (h.tmem.vmem j hj hv).2
  obtain ⟨z, hz, e0⟩ := children_eq h hj hs
  obtain ⟨X, Y, hX, hY, hs'⟩ := preImg_vh hv (vlenAt pb A[j]) (childHashes A K vals A[j])
  have hsha : (sha256 (vals j)).length = 32 := ArenaCore.sha256_length _
  have e1 := write_mid (e0.trans (hs' z)) (w := sha256 (vals j)) (by rw [hsha, hz])
  rw [hsha, hX, ← hs'] at e1
  have hvi := vh_in h hj hv
  obtain ⟨hcl, hc32⟩ := childHashes_len hw hvm hj
  refine ⟨trieSt_write_in h hj (by omega) (by omega) ⟨_, _, hsha, hcl, hc32, e1⟩, ?_, e1⟩
  intro x hx hxj hx1
  rw [readMem_writeMem_disjoint _ _ _ _ _ _ ?_]
  · exact hs x hx hxj hx1
  obtain ⟨p, q, hp, hq, hxp, hc, hps⟩ := parent_of hw hx1
  rw [hps, childSlot_eq]
  have hsi := slot_in h hp hq
  by_cases hpj : p = j
  · subst hpj; have := vh_lt_slot hv hq; omega
  · have := recs_disj hw hp hj hpj (a := A[p].pre + slotAt A[p].nf q) (b := A[j].pre + vhOff A[j].nf) (n := 32)
      (by omega) (by omega) (by omega) (by omega)
    omega

theorem fin_step {m1 : M} (h : TrieSt cb pb rs R A K vals m1) {j : Nat} (hj : j < A.length)
    (hs : SlotInv A K vals j m1.mem)
    (hr : readMem m1.mem A[j].pre A[j].preLen =
      preImg A[j].nf (vlenAt pb A[j]) (sha256 (vals j)) (childHashes A K vals A[j])) :
    TrieSt cb pb rs R A K vals
      ⟨m1.regs, writeMem m1.mem A[j].pslot 32 (sha256 (readMem m1.mem A[j].pre A[j].preLen))⟩ ∧
    SlotInv A K vals (j + 1) (writeMem m1.mem A[j].pslot 32 (sha256 (readMem m1.mem A[j].pre A[j].preLen))) ∧
    (j + 1 = A.length → readMem (writeMem m1.mem A[j].pslot 32 (sha256 (readMem m1.mem A[j].pre A[j].preLen)))
      C_ROOT 32 = (rootT A K vals).hashOf) := by
  have hw := h.tok.wf
  have hvm : ∀ j (h : j < A.length), hasVal A[j].nf = true → (vals j).length = vlenAt pb A[j] :=
    fun j hj hv => (h.tmem.vmem j hj hv).2
  have hH : sha256 (readMem m1.mem A[j].pre A[j].preLen) = (treeAt A K vals j).hashOf := by
    rw [hr, hashOf_treeAt hw (List.getElem?_eq_getElem hj) (hvm j hj)]
  have hHl : (treeAt A K vals j).hashOf.length = 32 := hashOf_length hw hvm hj
  rw [hH]
  -- slots of processed non-root entries are in preimages
  have slotx : ∀ x (hx : x < A.length), x + 1 < A.length → ∃ p q, ∃ hp : p < A.length, q < nKids A[p].nf ∧
      x < p ∧ childIdx K A[p].kid (nKids A[p].nf) q = x ∧ A[x].pslot = A[p].pre + slotAt A[p].nf q ∧
      slotAt A[p].nf q + 32 < A[p].preLen := by
    intro x hx hx1
    obtain ⟨p, q, hp, hq, hxp, hc, hps⟩ := parent_of hw hx1
    exact ⟨p, q, hp, hq, hxp, hc, by rw [hps, childSlot_eq], slot_in h hp hq⟩
  by_cases hroot : j + 1 = A.length
  · have hrs := hw.root_slot
    rw [getD_eq_get (by omega)] at hrs
    have hjr : A[j].pslot = C_ROOT := by
      have : j = A.length - 1 := by omega
      subst this; exact hrs
    rw [hjr]
    refine ⟨trieSt_write_root h _, ?_, fun _ => ?_⟩
    · intro x hx hxj hx1
      obtain ⟨p, q, hp, hq, hxp, hc, hps, hsi⟩ := slotx x hx hx1
      obtain ⟨-, hf1, hf2, -⟩ := ent_facts hw hp
      rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by rw [hps]; simp only [C_ROOT, PF] at hf1 ⊢; omega)]
      exact hs x hx (by omega) hx1
    · rw [read_write_self _ _ _ hHl]
      simp only [rootT]
      have : j = A.length - 1 := by omega
      rw [this]
  · obtain ⟨p, q, hp, hq, hjp, hcj, hpsj, hsij⟩ := slotx j hj (by omega)
    rw [hpsj]
    refine ⟨?_, ?_, fun h' => absurd h' hroot⟩
    · obtain ⟨z, zs, a1, a2, a3, a4⟩ := h.tmem.pmem p hp
      obtain ⟨X, Y, hX, hY, hset⟩ := preImg_slot (ent_facts hw hp).1 (vlenAt pb A[p]) a1 a2 a3 hq
      have hql : q < zs.length := by omega
      have e := hset (zs[q]'hql)
      rw [List.set_getElem_self] at e
      have e1 := write_mid (a4.trans e) (w := (treeAt A K vals j).hashOf)
        (by rw [hHl, a3 _ (List.getElem_mem hql)])
      rw [hHl, hX, ← hset] at e1
      refine trieSt_write_in h hp (by omega) (by omega) ⟨z, zs.set q (treeAt A K vals j).hashOf, a1,
        by rw [List.length_set, a2], ?_, e1⟩
      intro x hx
      rcases List.mem_or_eq_of_mem_set hx with hx | hx
      · exact a3 x hx
      · rw [hx]; exact hHl
    · intro x hx hxj hx1
      by_cases hxe : x = j
      · subst hxe; rw [hpsj, read_write_self _ _ _ hHl]
      · rw [readMem_writeMem_disjoint _ _ _ _ _ _ ?_]
        · exact hs x hx (by omega) hx1
        obtain ⟨p', q', hp', hq', hxp', hcx, hpsx, hsix⟩ := slotx x hx hx1
        rw [hpsx]
        by_cases hpp : p' = p
        · subst hpp
          rcases Nat.lt_trichotomy q' q with hqq | hqq | hqq
          · have := slot_lt hqq hq; omega
          · subst hqq; exact absurd (hcx.symm.trans hcj) hxe
          · have := slot_lt hqq hq'; omega
        · have := recs_disj hw hp' hp hpp (a := A[p'].pre + slotAt A[p'].nf q')
            (b := A[p].pre + slotAt A[p].nf q) (n := 32) (by omega) (by omega) (by omega) (by omega)
          omega

end

end ReexecNpai.HashAux
