import ReexecNpai.Spec.RecAux8

/-!
# Record parse: leaf record bodies (bytecode ↔ positional facts)
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-- The state at the start of a record body (after the kind dispatch). -/
structure RecStart (cb pb : Bytes) (rs : List Receipt) (R N o : Nat) (A : List Ent) (K S : List Nat)
    (m m1 : M) : Prop where
  inv : ParseInv cb pb rs R N o A K S m
  olt : o < pb.length
  cap : A.length < NCAP
  mem : m1.mem = m.mem
  r10 : m1.regs 10 = PF + o + 1
  r0 : m1.regs 0 = u8At pb o
  fr : ∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 10 → j ≠ 13 → m1.regs j = m.regs j

/-- Post-state of a record body. -/
def BodyPost (cb pb : Bytes) (rs : List Receipt) (R N o : Nat) (A : List Ent) (m2 : M) : Prop :=
  ∃ o' A' K' S0, PreInv cb pb rs R N o' A' K' S0 m2 ∧ A'.length = A.length + 1 ∧ o < o'

/-- Post-state of a record body ending at `o'`, with its cost. -/
def BodyPostT (cb pb : Bytes) (rs : List Receipt) (R N o o' : Nat) (A : List Ent) (m2 : M) (c : Nat) : Prop :=
  ∃ A' K' S0, PreInv cb pb rs R N o' A' K' S0 m2 ∧ A'.length = A.length + 1 ∧ o < o' ∧ c + 40 ≤ 80 * (o' - o)

theorem drop_inj {pb : Bytes} {a b : Nat} (ha : a ≤ pb.length) (hb : b ≤ pb.length) (h : pb.drop a = pb.drop b) :
    a = b := by
  have := congrArg List.length h
  simp at this; omega

/-! ## Reading the proof copy by absolute address -/

section
variable {M0 : Nat → UInt8} {pb : Bytes}

theorem byte_at (h : readMem M0 PF pb.length = pb) {a i : Nat} (ha : a = PF + i) (hi : i < pb.length) :
    (M0 a).toNat = u8At pb i := by
  subst ha; exact byteProof h hi

theorem rd_at (h : readMem M0 PF pb.length = pb) {m : M} (hm : m.mem = M0) {a i : Nat} (ha : a = PF + i)
    (hi : i + 4 ≤ pb.length) : rd32 m a = leAt pb i 4 := by
  subst ha; rw [rd32, hm]; exact rdmProof h hi

theorem rm_at (h : readMem M0 PF pb.length = pb) {a i n : Nat} (ha : a = PF + i) (hi : i + n ≤ pb.length) :
    readMem M0 a n = sl pb i n := by
  subst ha; exact rdProof' h hi

end

/-! ## Facts ↔ checks -/

theorem leafFacts_of_chk1 {pb : Bytes} {m : M} {o : Nat} (hpf : readMem m.mem PF pb.length = pb)
    (hd : readMem m.mem 0 168 = dataSeg) (hc : LeafChk1 m (PF + o + 1) (PF + pb.length)) :
    LeafFacts pb o true ∧ rd32 m (PF + o + 1) = leAt pb (o + 1) 4 ∧
      rd32 m (PF + o + 1 + 4 + rd32 m (PF + o + 1) + 1) = leAt pb (lpOf pb o true + 1) 4 := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := hc
  have hV := rd_at hpf rfl (show PF + o + 1 = PF + (o + 1) by omega) (by omega)
  rw [hV] at c2 c3 c4 c5 c6 c7 c8 ⊢
  have hlp : lpOf pb o true = o + 5 + leAt pb (o + 1) 4 := rfl
  have hH := rd_at hpf rfl (show PF + o + 1 + 4 + leAt pb (o + 1) 4 + 1 = PF + (o + 5 + leAt pb (o + 1) 4 + 1)
    by omega) (by omega)
  rw [hH] at c4 c5 c7 c8
  rw [byte_at hpf (show PF + o + 1 + 4 + leAt pb (o + 1) 4 = PF + (o + 5 + leAt pb (o + 1) 4) by omega)
    (by omega)] at c3
  rw [byte_at hpf (show PF + o + 1 + 4 + leAt pb (o + 1) 4 + 5 = PF + (o + 5 + leAt pb (o + 1) 4 + 5) by omega)
    (by omega)] at c6
  rw [rm_at hpf (show PF + o + 1 + 4 + leAt pb (o + 1) 4 + 5 + leAt pb (o + 5 + leAt pb (o + 1) 4 + 1) 4 =
    PF + (o + 5 + leAt pb (o + 1) 4 + 5 + leAt pb (o + 5 + leAt pb (o + 1) 4 + 1) 4) by omega) (by omega),
    rm_at hpf (show PF + o + 1 = PF + (o + 1) by omega) (by omega)] at c7
  rw [rm_at hpf (show PF + o + 1 + 4 + leAt pb (o + 1) 4 + 9 + leAt pb (o + 5 + leAt pb (o + 1) 4 + 1) 4 =
    PF + (o + 5 + leAt pb (o + 1) 4 + 9 + leAt pb (o + 5 + leAt pb (o + 1) 4 + 1) 4) by omega) (by omega),
    dZero hd] at c8
  have hl' : leAt pb (lpOf pb o true + 1) 4 = leAt pb (o + 5 + leAt pb (o + 1) 4 + 1) 4 := by rw [hlp]
  rw [hlp]
  exact ⟨⟨fun _ => by omega, by omega, c3, c4, by omega, c6, fun _ => c7, fun _ => c8⟩, rfl, hH⟩

theorem leafFacts_of_chk2 {pb : Bytes} {m : M} {o : Nat} (hpf : readMem m.mem PF pb.length = pb)
    (hc : LeafChk2 m (PF + o + 1) (PF + pb.length)) :
    LeafFacts pb o false ∧ rd32 m (PF + o + 1 + 1) = leAt pb (lpOf pb o false + 1) 4 := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := hc
  have hlp : lpOf pb o false = o + 1 := rfl
  have hH := rd_at hpf rfl (show PF + o + 1 + 1 = PF + (o + 1 + 1) by omega) (by omega)
  rw [hH] at c3 c4
  rw [byte_at hpf (show PF + o + 1 = PF + (o + 1) by omega) (by omega)] at c2
  rw [byte_at hpf (show PF + o + 1 + 5 = PF + (o + 1 + 5) by omega) (by omega)] at c5
  have hl' : leAt pb (lpOf pb o false + 1) 4 = leAt pb (o + 1 + 1) 4 := by rw [hlp]
  rw [hlp]
  exact ⟨⟨fun h => absurd h (by simp), by omega, c2, c3, by omega, c5, fun h => absurd h (by simp),
    fun h => absurd h (by simp)⟩, hH⟩

theorem chk1_of_leafFacts {pb : Bytes} {m : M} {o : Nat} (hpf : readMem m.mem PF pb.length = pb)
    (hd : readMem m.mem 0 168 = dataSeg) (hf : LeafFacts pb o true) :
    LeafChk1 m (PF + o + 1) (PF + pb.length) ∧ rd32 m (PF + o + 1) = leAt pb (o + 1) 4 ∧
      rd32 m (PF + o + 1 + 4 + rd32 m (PF + o + 1) + 1) = leAt pb (lpOf pb o true + 1) 4 := by
  obtain ⟨v5, p5, tag, hl1, hend, hp0, hlen, hzero⟩ := hf
  have hlp : lpOf pb o true = o + 5 + leAt pb (o + 1) 4 := rfl
  rw [hlp] at p5 tag hl1 hend hp0 hlen hzero
  have v5 := v5 rfl
  have hlen := hlen rfl
  have hzero := hzero rfl
  have hV := rd_at hpf rfl (show PF + o + 1 = PF + (o + 1) by omega) (by omega)
  have hH := rd_at hpf rfl (show PF + o + 1 + 4 + leAt pb (o + 1) 4 + 1 = PF + (o + 5 + leAt pb (o + 1) 4 + 1)
    by omega) (by omega)
  simp only [LeafChk1]
  rw [hV, hH, hlp]
  refine ⟨⟨by omega, by omega, ?_, hl1, by omega, ?_, ?_, ?_⟩, rfl, rfl⟩
  · rw [byte_at hpf (show PF + o + 1 + 4 + leAt pb (o + 1) 4 = PF + (o + 5 + leAt pb (o + 1) 4) by omega)
      (by omega)]; exact tag
  · rw [byte_at hpf (show PF + o + 1 + 4 + leAt pb (o + 1) 4 + 5 = PF + (o + 5 + leAt pb (o + 1) 4 + 5) by omega)
      (by omega)]; exact hp0
  · rw [rm_at hpf (show PF + o + 1 + 4 + leAt pb (o + 1) 4 + 5 + leAt pb (o + 5 + leAt pb (o + 1) 4 + 1) 4 =
      PF + (o + 5 + leAt pb (o + 1) 4 + 5 + leAt pb (o + 5 + leAt pb (o + 1) 4 + 1) 4) by omega) (by omega),
      rm_at hpf (show PF + o + 1 = PF + (o + 1) by omega) (by omega)]; exact hlen
  · rw [rm_at hpf (show PF + o + 1 + 4 + leAt pb (o + 1) 4 + 9 + leAt pb (o + 5 + leAt pb (o + 1) 4 + 1) 4 =
      PF + (o + 5 + leAt pb (o + 1) 4 + 9 + leAt pb (o + 5 + leAt pb (o + 1) 4 + 1) 4) by omega) (by omega),
      dZero hd]; exact hzero

theorem chk2_of_leafFacts {pb : Bytes} {m : M} {o : Nat} (hpf : readMem m.mem PF pb.length = pb)
    (hf : LeafFacts pb o false) :
    LeafChk2 m (PF + o + 1) (PF + pb.length) ∧ rd32 m (PF + o + 1 + 1) = leAt pb (lpOf pb o false + 1) 4 := by
  obtain ⟨-, p5, tag, hl1, hend, hp0, -, -⟩ := hf
  have hlp : lpOf pb o false = o + 1 := rfl
  rw [hlp] at p5 tag hl1 hend hp0
  have hH := rd_at hpf rfl (show PF + o + 1 + 1 = PF + (o + 1 + 1) by omega) (by omega)
  simp only [LeafChk2]
  rw [hH, hlp]
  refine ⟨⟨by omega, ?_, hl1, by omega, ?_⟩, rfl⟩
  · rw [byte_at hpf (show PF + o + 1 = PF + (o + 1) by omega) (by omega)]; exact tag
  · rw [byte_at hpf (show PF + o + 1 + 5 = PF + (o + 1 + 5) by omega) (by omega)]; exact hp0

/-! ## Leaf bodies -/

section
variable {pub cb pb : Bytes} {rs : List Receipt} {R N o : Nat} {A : List Ent} {K S : List Nat} {m m1 : M}

theorem RecStart.k1 (hs : RecStart cb pb rs R N o A K S m m1) : m1.regs 15 = 1 := by
  rw [hs.fr 15 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hs.inv.st.k1
theorem RecStart.k8 (hs : RecStart cb pb rs R N o A K S m m1) : m1.regs 14 = 8 := by
  rw [hs.fr 14 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hs.inv.st.k8
theorem RecStart.rE (hs : RecStart cb pb rs R N o A K S m m1) : m1.regs 9 = PF + pb.length := by
  rw [hs.fr 9 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hs.inv.rE
theorem RecStart.pf (hs : RecStart cb pb rs R N o A K S m m1) : readMem m1.mem PF pb.length = pb := by
  rw [hs.mem]; exact hs.inv.st.proof
theorem RecStart.data (hs : RecStart cb pb rs R N o A K S m m1) : readMem m1.mem 0 168 = dataSeg := by
  rw [hs.mem]; exact hs.inv.st.data
theorem RecStart.plen (hs : RecStart cb pb rs R N o A K S m m1) : PF + pb.length ≤ 13844304 := by
  have := hs.inv.st.plen; simp only [PMAX, PF] at this ⊢; omega
theorem RecStart.kc (hs : RecStart cb pb rs R N o A K S m m1) {m' : M} (hm : m'.mem = m1.mem) :
    rd32 m' C_KC = K.length := by
  rw [rd32_eq, hm, hs.mem, ← rd32_eq, hs.inv.kc]
theorem RecStart.regs (hs : RecStart cb pb rs R N o A K S m m1) :
    m1.regs 5 = revSum pb A ∧ m1.regs 7 = S.length ∧ m1.regs 8 = A.length ∧ m1.regs 14 = m.regs 14 ∧
      m1.regs 15 = m.regs 15 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hs.fr 5 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hs.inv.rrv
  · rw [hs.fr 7 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hs.inv.rsp
  · rw [hs.fr 8 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hs.inv.re
  · exact hs.fr 14 (by omega) (by omega) (by omega) (by omega) (by omega)
  · exact hs.fr 15 (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The writes and the arena step of a leaf, after its checks. -/
theorem leaf_tail {hv : Bool} (hs : RecStart cb pb rs R N o A K S m m1)
    (hk : u8At pb o = if hv then 1 else 2) (hf : LeafFacts pb o hv) {m' : M}
    (hm' : m'.mem = m1.mem) (r1 : m'.regs 1 = if hv then PF + o + 5 else 0)
    (r2 : m'.regs 2 = if hv then leAt pb (o + 1) 4 else 0)
    (r3 : m'.regs 3 = leAt pb (lpOf pb o hv + 1) 4 + 49) (r10 : m'.regs 10 = PF + lpOf pb o hv)
    (r5 : m'.regs 5 = m1.regs 5) (r7 : m'.regs 7 = m1.regs 7) (r8 : m'.regs 8 = m1.regs 8)
    (r9 : m'.regs 9 = m1.regs 9) (r14 : m'.regs 14 = 8) (r15 : m'.regs 15 = 1) :
    twp P (Inp pub cb pb) (seqs leafWrL) m' (fun m2 c => BodyPostT cb pb rs R N o
      (lpOf pb o hv + leAt pb (lpOf pb o hv + 1) 4 + 49) A m2 (c + 500)) := by
  have h := hs.inv
  obtain ⟨g5, g7, g8, g14, g15⟩ := hs.regs
  have hpl := hs.plen
  have hcap := hs.cap
  have hend := hf.hend
  have hlpo : o + 1 ≤ lpOf pb o hv := by cases hv <;> simp [lpOf] <;> omega
  have hrv : revSum pb A < 4294967296 := by
    have := revSum_le h; have := h.ole; simp only [PF] at hpl this; omega
  simp only [NCAP] at hcap
  refine twp_mono (leafWr_twp (e := A.length) (pre := PF + lpOf pb o hv)
    (pl := leAt pb (lpOf pb o hv + 1) 4 + 49) (val := if hv then PF + o + 5 else 0)
    (vl := if hv then leAt pb (o + 1) 4 else 0) (rv := revSum pb A) r15 r14 (by rw [r8, g8])
    (by simp only [NCAP]; omega) r10 r3 r1 r2 (by rw [r5, g5]) (by simp only [PF] at hpl ⊢; omega)
    (by have := leAt4_lt pb (lpOf pb o hv + 1); omega) (by cases hv <;> simp [PF] at hpl ⊢ <;> omega)
    (by cases hv <;> simp <;> exact leAt4_lt _ _) hrv) ?_
  rintro m2 c ⟨hmem, h10, h5, h7, h8, h9, h14, h15, hc⟩
  rw [hs.kc hm'] at hmem
  rw [hm', hs.mem] at hmem
  obtain ⟨A', K', S0, hpre, hlen, hoo⟩ := leaf_step h hs.cap hk hf hmem (by rw [h10]; try omega)
    (by rw [h5]; try (cases hv <;> simp)) (by rw [h7, r7, g7]) h8 (by rw [h9, r9, hs.rE])
    (by rw [h14, g14.symm, hs.k8]) (by rw [h15, g15.symm, hs.k1])
  refine ⟨A', K', S0, hpre, hlen, hoo, ?_⟩
  have : o + 51 ≤ lpOf pb o hv + leAt pb (lpOf pb o hv + 1) 4 + 49 := by
    have := hf.hl1; cases hv <;> simp [lpOf] at this ⊢ <;> omega
  omega

theorem BodyPostT.mono {o o' : Nat} {m2 : M} {c c' : Nat} (h : BodyPostT cb pb rs R N o o' A m2 c) (hc : c' ≤ c) :
    BodyPostT cb pb rs R N o o' A m2 c' := by
  obtain ⟨A', K', S0, a, b, d, e⟩ := h
  exact ⟨A', K', S0, a, b, d, by omega⟩

theorem BodyPostT.post {o o' : Nat} {m2 : M} {c : Nat} (h : BodyPostT cb pb rs R N o o' A m2 c) :
    BodyPost cb pb rs R N o A m2 := by
  obtain ⟨A', K', S0, a, b, d, -⟩ := h
  exact ⟨o', A', K', S0, a, b, d⟩

theorem leaf_body_wp {hv : Bool} (hs : RecStart cb pb rs R N o A K S m m1)
    (hk : u8At pb o = if hv then 1 else 2) :
    wp P (Inp pub cb pb) pLeaf m1 (BodyPost cb pb rs R N o A) := by
  have hq : PF + o + 1 ≤ PF + pb.length := by have := hs.olt; omega
  rw [pLeaf_split, rec_wp_seqs_append _ _ (by simp [leafChkL]) (by simp [leafWrL])]
  cases hv
  · refine wp_mono (leafChk2_wp hs.k1 hs.k8 hs.r10 hs.plen hs.rE (by rw [hs.r0, hk]; rfl) hq) ?_
    rintro m' ⟨hc, hm', -, r1, r2, r3, r10, r5, r7, r8, r9, r14, r15⟩
    obtain ⟨hf, hH⟩ := leafFacts_of_chk2 hs.pf hc
    exact wp_of_spec (leaf_tail hs hk hf hm' (by rw [r1]; rfl) (by rw [r2]; rfl) (by rw [r3, hH])
      (by rw [r10]; rfl) r5 r7 r8 r9 r14 r15) (fun m2 c hp => hp.post)
  · refine wp_mono (leafChk1_wp hs.k1 hs.k8 hs.r10 hs.plen hs.rE (by rw [hs.r0, hk]; rfl) hq) ?_
    rintro m' ⟨hc, hm', -, r1, r2, r3, r10, r5, r7, r8, r9, r14, r15⟩
    obtain ⟨hf, hV, hH⟩ := leafFacts_of_chk1 hs.pf hs.data hc
    exact wp_of_spec (leaf_tail hs hk hf hm' (by rw [r1]; simp; try omega) (by rw [r2, hV]; rfl) (by rw [r3, hH])
      (by rw [r10, hV]; simp [lpOf]; omega) r5 r7 r8 r9 r14 r15) (fun m2 c hp => hp.post)

theorem leafPos_of_rec {hv : Bool} {o : Nat} (hk : u8At pb o = if hv then 1 else 2) (hlt : o < pb.length)
    (stk : List PTrie) : recPos pb o stk = leafPos pb hv (o + 1) stk := by
  unfold recPos
  rw [if_pos (by omega)]
  cases hv
  · simp only [hk, Bool.false_eq_true, ↓reduceIte, show ¬ (2 = 1) from by decide]
  · simp only [hk, ↓reduceIte]

theorem leaf_body_twp {hv : Bool} (hs : RecStart cb pb rs R N o A K S m m1)
    (hk : u8At pb o = if hv then 1 else 2) {stk' : List PTrie} {o' : Nat}
    (hd : decRec ((S.map (treeAt A K (vals0 pb A))).reverse) (pb.drop o) = some (stk', pb.drop o'))
    (ho' : o' ≤ pb.length) :
    twp P (Inp pub cb pb) pLeaf m1 (fun m2 c => BodyPostT cb pb rs R N o o' A m2 (c + 100)) := by
  rw [decRec_pos, leafPos_of_rec hk hs.olt] at hd
  cases hr : leafPos pb hv (o + 1) ((S.map (treeAt A K (vals0 pb A))).reverse) with
  | none => rw [hr] at hd; simp at hd
  | some x =>
  obtain ⟨stk'', o''⟩ := x
  rw [hr] at hd
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨hf, ho''⟩ := leafFacts_of_pos hr
  have := hf.hend
  have he : o'' = o' := drop_inj (by omega) ho' hd.2
  subst he
  rw [ho'']
  rw [pLeaf_split, rec_twp_seqs_append _ _ (by simp [leafChkL]) (by simp [leafWrL])]
  have hq : PF + o + 1 ≤ PF + pb.length := by have := hs.olt; omega
  cases hv
  · obtain ⟨hc, hH⟩ := chk2_of_leafFacts hs.pf hf
    refine twp_mono (leafChk2_twp hs.k1 hs.k8 hs.r10 hs.plen hs.rE (by rw [hs.r0, hk]; rfl) hq hc) ?_
    rintro m' c1 ⟨⟨hm', -, r1, r2, r3, r10, r5, r7, r8, r9, r14, r15⟩, hc1⟩
    refine twp_mono (leaf_tail hs hk hf hm' (by rw [r1]; rfl) (by rw [r2]; rfl) (by rw [r3, hH])
      (by rw [r10]; rfl) r5 r7 r8 r9 r14 r15) ?_
    intro m2 c2 hp
    exact hp.mono (by omega)
  · obtain ⟨hc, hV, hH⟩ := chk1_of_leafFacts hs.pf hs.data hf
    refine twp_mono (leafChk1_twp hs.k1 hs.k8 hs.r10 hs.plen hs.rE (by rw [hs.r0, hk]; rfl) hq hc) ?_
    rintro m' c1 ⟨⟨hm', -, r1, r2, r3, r10, r5, r7, r8, r9, r14, r15⟩, hc1⟩
    refine twp_mono (leaf_tail hs hk hf hm' (by rw [r1]; simp; try omega) (by rw [r2, hV]; rfl) (by rw [r3, hH])
      (by rw [r10, hV]; simp [lpOf]; omega) r5 r7 r8 r9 r14 r15) ?_
    intro m2 c2 hp
    exact hp.mono (by omega)

end

end ReexecNpai
