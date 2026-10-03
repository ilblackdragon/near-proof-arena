import ReexecNpai.Spec.HashAux

/-!
# Phase spec: the hash pass and the root comparison

`pHash` runs over the arena entries in order (post-order: children before
parents). For entry `j` it writes the value hash into the value-hash
placeholder (if the node carries a revealed value), then hashes the preimage
into `pslot` (a child slot of the parent's preimage, or `C_ROOT` for the
root). The loop invariant (`HInv`) is `TrieSt` plus `SlotInv` (the hash slots
of the processed non-root entries hold their hashes) plus the root hash once
all entries are done. The geometry and preimage-layout lemmas are in
`Spec/HashAux.lean`.
-/

set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false

namespace ReexecNpai.HashAux

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-! ## A counted loop with a variable per-iteration cost -/

section
variable {p : Program} {inp : Inputs}

theorem twp_forUp_var {i n t : Nat} {body : Stmt} (hit : i ≠ t) (hnt : n ≠ t) (hin : i ≠ n) {m : M}
    {Q : M → Nat → Prop} (J : Nat → M → Prop) (N : Nat) (F : Nat → Nat) (hN : N < 18446744073709551616)
    (hJ : ∀ j m v w, J j m → J j { m with regs := setReg (setReg m.regs i v) t w })
    (h0 : J 0 m) (hi0 : m.regs i = 0) (hn0 : m.regs n = N)
    (hbody : ∀ j m, j < N → J j m → m.regs i = j → m.regs n = N →
      twp p inp body m (fun m' c => J (j + 1) m' ∧ m'.regs i = j ∧ m'.regs n = N ∧ c + 4 + F (j + 1) ≤ F j))
    (hq : ∀ m c, J N m → m.regs n = N → c ≤ F 0 + 2 → Q m c) :
    twp p inp (forUp i n t body) m Q := by
  let m0 : M := { m with regs := setReg m.regs t (if 0 < N then 1 else 0) }
  have e0 : Ev p inp (.op (.bin .ltu t i n)) m (.ok m0) 1 :=
    Ev.op rfl (by simp [ins, m0, hi0, hn0, eval_ltu])
  let I : M → Prop := fun x => ∃ j, j ≤ N ∧ J j x ∧ x.regs i = j ∧ x.regs n = N ∧
    x.regs t = (if j < N then 1 else 0)
  have hI0 : I m0 := ⟨0, Nat.zero_le _, by
    have := hJ 0 m 0 (if 0 < N then 1 else 0) h0
    have e : setReg (setReg m.regs i 0) t (if 0 < N then 1 else 0) = setReg m.regs t (if 0 < N then 1 else 0) := by
      funext r; simp only [setReg_apply]
      by_cases h1 : r = t
      · simp [h1]
      · by_cases h2 : r = i
        · subst h2; simp [h1, hi0]
        · simp [h1, h2]
    rw [e] at this; exact this, by simp [m0, setReg_apply, hit, hi0],
      by simp [m0, setReg_apply, hnt, hn0], by simp [m0]⟩
  have hl : twp p inp (.loop t (.seq body (.seq (.op (.addi i i 1)) (.op (.bin .ltu t i n))))) m0
      (fun m' c => Q m' (1 + c)) := by
    apply twp_loop I (fun x => F (x.regs i)) hI0
    · intro x ⟨j, hjN, hJx, hix, hnx, htx⟩ ht
      have hjN' : j < N := by
        rcases Nat.lt_or_ge j N with h | h
        · exact h
        · rw [htx] at ht; simp [Nat.not_lt.mpr h] at ht
      obtain ⟨x1, c1, h1, hJ1, hi1, hn1, hc1⟩ := hbody j x hjN' hJx hix hnx
      refine ⟨_, _, Ev.seqOk h1 (forUp_tail hit hnt hin x1 j N hi1 hn1 hjN' hN), ⟨j + 1, hjN', hJ _ _ _ _ hJ1,
        by simp [setReg_apply, hit], by simp [setReg_apply, hnt, hin.symm, hn1], by simp⟩, ?_⟩
      simp only [setReg_apply, hit, ↓reduceIte, hix]
      omega
    · intro x c ⟨j, hj, hJ2, hi2, hn2, ht2⟩ hz hc
      have hjN : j = N := by
        rcases Nat.lt_or_ge j N with h | h
        · rw [ht2] at hz; simp [h] at hz
        · omega
      subst hjN
      have hm0i : m0.regs i = 0 := by simp [m0, setReg_apply, hit, hi0]
      simp only [hm0i] at hc
      exact hq x _ hJ2 hn2 (by omega)
  obtain ⟨m', c, e, hq'⟩ := hl
  exact ⟨m', 1 + c, Ev.seqOk e0 e, hq'⟩

end

/-! ## The loop body -/

section
variable {pub cb pb : Bytes}

def hL : Stmt := seqs [ADDI 2 1 1, ld32 4 2, ADD 4 4 1, ADDI 4 4 9]
def hS : Stmt := seqs [CST 2 4, SUB 2 3 2, ld32 5 2, SHA 4 3 5]
def hT : Stmt := seqs [LD8 2 1, .ite 2 (ADDI 4 1 5) hL, hS]

theorem hL_twp {m : M} {pre hl : Nat} (hk8 : m.regs 14 = 8) (h1 : m.regs 1 = pre)
    (hpre : pre + 5 ≤ MEMSIZE) (hhl : (readMem m.mem (pre + 1) 4).leToNat = hl) (hlb : hl < 4294967296) :
    twp P (Inp pub cb pb) hL m (fun m' c => m'.mem = m.mem ∧ m'.regs 4 = hl + pre + 9 ∧
      (∀ r, r ≠ 2 → r ≠ 4 → r ≠ 12 → m'.regs r = m.regs r) ∧ c = 17) := by
  simp only [MEMSIZE] at hpre
  simp only [hL]
  npai_vc [hk8, h1, hhl, ne_eq]
  intro r h2 h4 h12; simp [h2, h4, h12]

theorem hS_twp {m : M} {val vl vh : Nat} (hk8 : m.regs 14 = 8) (h4 : m.regs 4 = vh) (h3 : m.regs 3 = val)
    (hval : 4 ≤ val) (hvl : val + vl ≤ MEMSIZE) (hvh : vh + 32 ≤ MEMSIZE)
    (hvlr : (readMem m.mem (val - 4) 4).leToNat = vl) :
    twp P (Inp pub cb pb) hS m (fun m' c => m'.mem = writeMem m.mem vh 32 (sha256 (readMem m.mem val vl)) ∧
      (∀ r, r ≠ 2 → r ≠ 4 → r ≠ 5 → r ≠ 12 → r ≠ 13 → m'.regs r = m.regs r) ∧ c = 17 + vl / 64) := by
  simp only [MEMSIZE] at hvl hvh
  simp only [hS]
  npai_vc [hk8, h4, h3, hvlr, ne_eq]
  exact ⟨hvl, by omega, fun r h2 h4 h5 h12 h13 => by simp [h2, h4, h5, h12, h13], by omega⟩

theorem hT_twp {m : M} {pre val vl vh : Nat} (hk8 : m.regs 14 = 8) (h1 : m.regs 1 = pre) (h3 : m.regs 3 = val)
    (hpre : pre + 5 ≤ MEMSIZE) (hval : 4 ≤ val) (hvl : val + vl ≤ MEMSIZE) (hvh : vh + 32 ≤ MEMSIZE)
    (hvlr : (readMem m.mem (val - 4) 4).leToNat = vl)
    (hvh1 : (m.mem pre).toNat ≠ 0 → vh = pre + 5)
    (hvh2 : (m.mem pre).toNat = 0 → (readMem m.mem (pre + 1) 4).leToNat + pre + 9 = vh) :
    twp P (Inp pub cb pb) hT m (fun m' c => m'.mem = writeMem m.mem vh 32 (sha256 (readMem m.mem val vl)) ∧
      (∀ r, r ≠ 2 → r ≠ 4 → r ≠ 5 → r ≠ 12 → r ≠ 13 → m'.regs r = m.regs r) ∧ c ≤ 40 + vl / 64) := by
  have hpre' := hpre
  simp only [MEMSIZE] at hpre'
  simp only [hT]
  npai_vc [hk8, h1, ne_eq]
  by_cases ht : (m.mem pre).toNat = 0
  · refine .inl ⟨ht, ?_⟩
    have hlb : (readMem m.mem (pre + 1) 4).leToNat < 4294967296 := by
      have := leToNat_lt (readMem m.mem (pre + 1) 4); simpa using this
    obtain ⟨m', c, e, hm', h4', hr', hc⟩ := hL_twp (pub := pub) (cb := cb) (pb := pb)
      (m := { regs := setReg m.regs 2 (m.mem pre).toNat, mem := m.mem })
      (by simp [setReg_apply, hk8]) (by simp [setReg_apply, h1]) hpre rfl hlb
    refine ⟨m', c, e, ?_⟩
    obtain ⟨m2, c2, e2, hm2, hr2, hc2⟩ := hS_twp (pub := pub) (cb := cb) (pb := pb) (m := m') (val := val)
      (vl := vl) (vh := vh) (by rw [hr' 14 (by decide) (by decide) (by decide)]; simp [setReg_apply, hk8])
      (by rw [h4', hvh2 ht])
      (by rw [hr' 3 (by decide) (by decide) (by decide)]; simp [setReg_apply, h3]) hval hvl hvh
      (by rw [hm']; exact hvlr)
    refine ⟨m2, c2, e2, by rw [hm2, hm'], fun r a2 a4 a5 a12 a13 => ?_, by omega⟩
    rw [hr2 r a2 a4 a5 a12 a13, hr' r a2 a4 a12]; simp [setReg_apply, a2]
  · refine .inr ⟨ht, ?_⟩
    obtain ⟨m2, c2, e2, hm2, hr2, hc2⟩ := hS_twp (pub := pub) (cb := cb) (pb := pb)
      (m := { regs := setReg (setReg m.regs 2 (m.mem pre).toNat) 4 (pre + 5), mem := m.mem }) (val := val)
      (vl := vl) (vh := vh) (by simp [setReg_apply, hk8]) (by simp [setReg_apply, hvh1 ht])
      (by simp [setReg_apply, h3]) hval hvl hvh hvlr
    refine ⟨m2, c2, e2, hm2, fun r a2 a4 a5 a12 a13 => ?_, by omega⟩
    rw [hr2 r a2 a4 a5 a12 a13]; simp [setReg_apply, a2, a4]

def hC : Stmt := seqs [ADDI 2 0 4, ld32 4 2, ADDI 2 0 8, ld32 5 2, SHA 5 1 4]
def hBody : Stmt := seqs [CST 0 24, MUL 0 8 0, ADDI 0 0 AR, ld32 1 0, ADDI 2 0 20, ld32 3 2, .ite 3 hT nop, hC]

theorem pHash_eq : pHash = seqs [ldCell 7 C_NODES, CST 8 0, forUp 8 7 6 hBody] := rfl

theorem hC_twp {m : M} {a0 pre plen ps : Nat} (hk8 : m.regs 14 = 8) (h0 : m.regs 0 = a0) (h1 : m.regs 1 = pre)
    (ha0 : a0 + 12 ≤ MEMSIZE)
    (hlen : (readMem m.mem (a0 + 4) 4).leToNat = plen)
    (hps : (readMem m.mem (a0 + 8) 4).leToNat = ps)
    (hb1 : pre + plen ≤ MEMSIZE) (hb2 : ps + 32 ≤ MEMSIZE) :
    twp P (Inp pub cb pb) hC m (fun m' c => m'.mem = writeMem m.mem ps 32 (sha256 (readMem m.mem pre plen)) ∧
      (∀ r, r ≠ 2 → r ≠ 4 → r ≠ 5 → r ≠ 12 → r ≠ 13 → m'.regs r = m.regs r) ∧ c = 31 + plen / 64) := by
  simp only [MEMSIZE] at hb1 hb2 ha0
  simp only [hC]
  npai_vc [hk8, h0, h1, hlen, hps, ne_eq]
  exact ⟨hb1, by omega, fun r a2 a4 a5 a12 a13 => by simp [a2, a4, a5, a12, a13], by omega⟩

theorem hash_leToNat_eq_leNat : ∀ l : Bytes, ArenaCore.Bytes.leToNat l = NearSpec.leNat l
  | [] => rfl
  | x :: xs => by simp [ArenaCore.Bytes.leToNat, NearSpec.leNat, hash_leToNat_eq_leNat xs]

theorem hash_leToNat_leN : ∀ (w x : Nat), x < 256 ^ w → ArenaCore.Bytes.leToNat (NearSpec.leN w x) = x
  | 0, x, h => by simp at h; simp [NearSpec.leN, ArenaCore.Bytes.leToNat, h]
  | w + 1, x, h => by
    simp only [NearSpec.leN, ArenaCore.Bytes.leToNat]
    have h' : x / 256 < 256 ^ w := by
      rw [Nat.pow_succ] at h; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    rw [hash_leToNat_leN w _ h']
    have : (UInt8.ofNat (x % 256)).toNat = x % 256 := by simp
    rw [this]; omega

theorem tag_facts {M0 : Nat → UInt8} {a n : Nat} {nf : NF} {vlen : Nat} {z : Bytes} {zs : List Bytes}
    (hm : readMem M0 a n = preImg nf vlen z zs) (hv : hasVal nf = true) (hok : NFOk nf) :
    ((M0 a).toNat ≠ 0 → vhOff nf = 5) ∧ ((M0 a).toNat = 0 → (readMem M0 (a + 1) 4).leToNat + 9 = vhOff nf) := by
  cases nf with
  | leaf k ref mm =>
    cases ref with
    | some _ => simp [hasVal] at hv
    | none =>
      have h' : readMem M0 a n = [0] ++ u32 (hexPrefix k true).length ++
          (hexPrefix k true ++ (u32 vlen ++ z) ++ u64 mm) := by rw [hm]; simp [preImg]
      have h1 := (read_split h').2.1
      have h2 := read_mid h'
      simp only [List.length_cons, List.length_nil, u32_length] at h1 h2
      rw [readMem_one] at h1
      have h0 : M0 a = 0 := by simpa using h1
      refine ⟨fun h => by simp [h0] at h, fun _ => ?_⟩
      rw [h2, u32, hash_leToNat_leN _ _ (by have := hok.2.1; simpa using this)]
      simp [vhOff]; omega
  | ext k h mm => simp [hasVal] at hv
  | branch v ks mm =>
    rcases v with _ | _ | _
    · simp [hasVal] at hv
    · have h' : readMem M0 a n = [] ++ [2] ++ (u32 vlen ++ z ++ u16 (bitsPres ks 0) ++ slotBytes ks zs ++ u64 mm) := by
        rw [hm]; simp [preImg]
      have h1 := (read_split h').2.2.1
      simp only [List.length_cons, List.length_nil, Nat.add_zero] at h1
      rw [readMem_one] at h1
      have h0 : M0 a = 2 := by simpa using h1
      exact ⟨fun _ => rfl, fun h => by simp [h0] at h⟩
    · simp [hasVal] at hv

theorem step_twp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes}
    (h : TrieSt cb pb rs R A K vals m) {j : Nat} (hj : j < A.length) (hs : SlotInv A K vals j m.mem)
    (hi : m.regs 8 = j) :
    twp P (Inp pub cb pb) hBody m (fun m' c => TrieSt cb pb rs R A K vals m' ∧ SlotInv A K vals (j + 1) m'.mem ∧
      (j + 1 = A.length → readMem m'.mem C_ROOT 32 = (rootT A K vals).hashOf) ∧
      m'.regs 8 = j ∧ m'.regs 7 = m.regs 7 ∧ HashFrame m m' ∧
      c + 4 ≤ 20 * (A[j].pre + A[j].preLen - A[j].rst)) := by
  have hw := h.tok.wf
  obtain ⟨a1, a2, a3, -, -, a6⟩ := h.tmem.amem j hj
  have hN := hw.len_le
  simp only [NCAP] at hN
  have hjN : j < 272728 := by omega
  have cv : ∀ k, j * 24 + 117000 + k = AR + 24 * j + k := fun k => by simp only [AR]; omega
  have hpre : (readMem m.mem (j * 24 + 117000) 4).leToNat = A[j].pre := by
    have := cv 0; simp only [Nat.add_zero] at this; rw [this]; exact a1
  have hval : (readMem m.mem (j * 24 + 117000 + 20) 4).leToNat = A[j].val := by rw [cv]; exact a6
  have hk8 := h.k8
  have hk1 := h.k1
  simp only [hBody]
  npai_vc [hk1, hk8, hi, hpre, hval, ne_eq]
  obtain ⟨hok, hpf, hrl, hend, hvt, hvf⟩ := ent_facts hw hj
  have hplen := h.plen
  simp only [PMAX] at hplen
  simp only [PF] at hpf hend
  have hlenE : (readMem m.mem (j * 24 + 117000 + 4) 4).leToNat = A[j].preLen := by rw [cv]; exact a2
  have hpsE : (readMem m.mem (j * 24 + 117000 + 8) 4).leToNat = A[j].pslot := by rw [cv]; exact a3
  have hL9 : 9 ≤ A[j].preLen := by
    obtain ⟨z, zs, -, -, -, e4⟩ := h.tmem.pmem j hj
    have e5 := congrArg List.length e4
    rw [readMem_length] at e5
    have := preImg_len A[j].nf (vlenAt pb A[j]) z zs
    omega
  have hpsl : A[j].pslot = 3136 ∨ 8844304 ≤ A[j].pslot := by
    by_cases hroot : j + 1 = A.length
    · have hrs := hw.root_slot
      rw [getD_eq_get (by omega)] at hrs
      have : j = A.length - 1 := by omega
      subst this; rw [hrs]; simp [C_ROOT]
    · obtain ⟨p, q, hp, hq, -, -, hpsl⟩ := parent_of hw (x := j) (by omega)
      rw [hpsl, childSlot_eq]
      obtain ⟨-, hf1, hf2, -⟩ := ent_facts hw hp
      simp only [PF] at hf1
      omega
  have hfr : ∀ (M1 : Nat → UInt8) (m2 : M) (w : Bytes), (∀ a, a < 8844304 → M1 a = m.mem a) →
      m2.mem = writeMem M1 A[j].pslot 32 w → HashFrame m m2 := by
    intro M1 m2 w h1 hm2 a ha hc
    simp only [PF, C_ROOT] at ha hc
    rw [hm2, writeMem_apply_out _ _ _ _ _ (by omega), h1 a ha]
  have hps : A[j].pslot + 32 ≤ 13844304 := by
    by_cases hroot : j + 1 = A.length
    · have hrs := hw.root_slot
      rw [getD_eq_get (by omega)] at hrs
      have : j = A.length - 1 := by omega
      subst this; rw [hrs]; simp [C_ROOT]
    · obtain ⟨p, q, hp, hq, -, -, hpsl⟩ := parent_of hw (x := j) (by omega)
      rw [hpsl, childSlot_eq]
      have := slot_in h hp hq
      have := end_le hw hp
      simp only [PF] at this
      omega
  have fin : ∀ (M1 : Nat → UInt8) (m2 : M), TrieSt cb pb rs R A K vals ⟨m.regs, M1⟩ → SlotInv A K vals j M1 →
      readMem M1 A[j].pre A[j].preLen =
        preImg A[j].nf (vlenAt pb A[j]) (sha256 (vals j)) (childHashes A K vals A[j]) →
      m2.mem = writeMem M1 A[j].pslot 32 (sha256 (readMem M1 A[j].pre A[j].preLen)) →
      m2.regs 14 = 8 → m2.regs 15 = 1 →
      TrieSt cb pb rs R A K vals m2 ∧ SlotInv A K vals (j + 1) m2.mem ∧
        (j + 1 = A.length → readMem m2.mem 3136 32 = (rootT A K vals).hashOf) := by
    intro M1 m2 t1 s1 r1 hm2 h14 h15
    obtain ⟨f1, f2, f3⟩ := fin_step (m1 := ⟨m.regs, M1⟩) t1 hj s1 r1
    exact ⟨trieSt_regs f1 hm2 h14 h15, by rw [hm2]; exact f2, by rw [hm2]; exact f3⟩
  by_cases hv : hasVal (A[j]'hj).nf = true
  · obtain ⟨hv1, hv2, hv3⟩ := hvt hv
    refine .inr ⟨by omega, ?_⟩
    have tf : ((m.mem (A[j]'hj).pre).toNat ≠ 0 → vhOff (A[j]'hj).nf = 5) ∧
        ((m.mem (A[j]'hj).pre).toNat = 0 → (readMem m.mem ((A[j]'hj).pre + 1) 4).leToNat + 9 = vhOff (A[j]'hj).nf) := by
      obtain ⟨z, zs, -, -, -, e4⟩ := h.tmem.pmem j hj
      exact tag_facts e4 hv hok
    have hvi := vh_in h hj hv
    refine twp_mono (hT_twp (pre := (A[j]'hj).pre) (val := (A[j]'hj).val) (vl := vlenAt pb (A[j]'hj))
      (vh := (A[j]'hj).pre + vhOff (A[j]'hj).nf) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
      (by simp [setReg_apply]) (by simp only [MEMSIZE]; omega) (by omega) (by simp only [MEMSIZE]; omega)
      (by simp only [MEMSIZE]; omega) ?_ ?_ ?_) ?_
    · simp only
      rw [h.tmem.lmem j hj hv, hash_leToNat_eq_leNat]; rfl
    · intro h0; simp only at h0; rw [tf.1 h0]
    · intro h0; simp only at h0 ⊢; have := tf.2 h0; omega
    intro m' c ⟨hm', hr', hc'⟩
    simp only at hm'
    rw [(h.tmem.vmem j hj hv).1] at hm'
    have rd : ∀ k, k ≤ 8 → readMem m'.mem (j * 24 + 117000 + k) 4 = readMem m.mem (j * 24 + 117000 + k) 4 := by
      intro k hk; rw [hm', readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)]
    refine twp_mono (hC_twp (a0 := j * 24 + 117000) (pre := (A[j]'hj).pre) (plen := (A[j]'hj).preLen) (ps := (A[j]'hj).pslot)
      (by rw [hr' 14 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [setReg_apply, hk8])
      (by rw [hr' 0 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [setReg_apply])
      (by rw [hr' 1 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [setReg_apply])
      (by simp only [MEMSIZE]; omega) (by rw [rd 4 (by omega)]; exact hlenE) (by rw [rd 8 (by omega)]; exact hpsE)
      (by simp only [MEMSIZE]; omega) (by simp only [MEMSIZE]; omega)) ?_
    intro m2 c2 ⟨hm2, hr2, hc2⟩
    obtain ⟨t1, s1, r1⟩ := mid_val h hj hs hv
    rw [hm'] at hm2
    have g8 : m2.regs 8 = j := by
      rw [hr2 8 (by decide) (by decide) (by decide) (by decide) (by decide),
        hr' 8 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [setReg_apply, hi]
    have g7 : m2.regs 7 = m.regs 7 := by
      rw [hr2 7 (by decide) (by decide) (by decide) (by decide) (by decide),
        hr' 7 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [setReg_apply]
    have g14 : m2.regs 14 = 8 := by
      rw [hr2 14 (by decide) (by decide) (by decide) (by decide) (by decide),
        hr' 14 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [setReg_apply, hk8]
    have g15 : m2.regs 15 = 1 := by
      rw [hr2 15 (by decide) (by decide) (by decide) (by decide) (by decide),
        hr' 15 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [setReg_apply, hk1]
    obtain ⟨f1, f2, f3⟩ := fin _ m2 t1 s1 r1 hm2 g14 g15
    refine ⟨f1, f2, f3, g8, g7, hfr _ m2 _ (fun a ha => ?_) hm2, by omega⟩
    rw [writeMem_apply_out _ _ _ _ _ (by omega)]
  · have hv' : hasVal (A[j]'hj).nf = false := by simpa using hv
    refine .inl ⟨hvf hv', ?_⟩
    refine twp_mono (hC_twp (a0 := j * 24 + 117000) (pre := (A[j]'hj).pre) (plen := (A[j]'hj).preLen) (ps := (A[j]'hj).pslot)
      (by simp [setReg_apply, hk8]) (by simp [setReg_apply]) (by simp [setReg_apply])
      (by simp only [MEMSIZE]; omega) hlenE hpsE (by simp only [MEMSIZE]; omega) (by simp only [MEMSIZE]; omega)) ?_
    intro m2 c2 ⟨hm2, hr2, hc2⟩
    simp only at hm2
    obtain ⟨z, hz, e0⟩ := children_eq h hj hs
    rw [preImg_novh hv' _ z (sha256 (vals j))] at e0
    have t1 : TrieSt cb pb rs R A K vals ⟨m.regs, m.mem⟩ := h
    have g8 : m2.regs 8 = j := by
      rw [hr2 8 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [setReg_apply, hi]
    have g7 : m2.regs 7 = m.regs 7 := by
      rw [hr2 7 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [setReg_apply]
    have g14 : m2.regs 14 = 8 := by
      rw [hr2 14 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [setReg_apply, hk8]
    have g15 : m2.regs 15 = 1 := by
      rw [hr2 15 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [setReg_apply, hk1]
    obtain ⟨f1, f2, f3⟩ := fin _ m2 t1 hs e0 hm2 g14 g15
    exact ⟨f1, f2, f3, g8, g7, hfr _ m2 _ (fun _ _ => rfl) hm2, by omega⟩

end

end ReexecNpai.HashAux

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1 HashAux

/-! ## Phase theorems -/

section
variable {pub cb pb : Bytes}

theorem hash_twp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes}
    (h : TrieSt cb pb rs R A K vals m) :
    twp P (Inp pub cb pb) pHash m (fun m' c => TrieSt cb pb rs R A K vals m' ∧
      readMem m'.mem C_ROOT 32 = (rootT A K vals).hashOf ∧ HashFrame m m' ∧ c ≤ 20 * pb.length + 10000) := by
  have hw := h.tok.wf
  have hk8 := h.k8
  have hk1 := h.k1
  have hnodes : (readMem m.mem 3120 4).leToNat = A.length := h.tmem.nodes
  have hN := hw.len_le
  have hpos := hw.len_pos
  have hplen := h.plen
  simp only [NCAP] at hN
  simp only [PMAX] at hplen
  rw [pHash_eq]
  simp only [seqs, ldCell]
  npai_vc [hk8, hk1, hnodes]
  apply twp_forUp_var (by decide) (by decide) (by decide)
    (fun j x => TrieSt cb pb rs R A K vals x ∧ SlotInv A K vals j x.mem ∧
      (j = A.length → readMem x.mem C_ROOT 32 = (rootT A K vals).hashOf) ∧ HashFrame m x) A.length
    (fun j => 20 * (PF + pb.length - (if j < A.length then (A.getD j default).rst else PF + pb.length)))
    (by omega)
  · intro j x v w ⟨t, s, r, f⟩
    exact ⟨trieSt_regs t rfl (by simp [setReg_apply, t.k8]) (by simp [setReg_apply, t.k1]), s, r, f⟩
  · refine ⟨trieSt_regs h rfl (by simp [setReg_apply, hk8]) (by simp [setReg_apply, hk1]),
      fun x _ hx => absurd hx (Nat.not_lt_zero _), fun e => by omega, fun _ _ _ => rfl⟩
  · simp [setReg_apply]
  · simp [setReg_apply]
  · intro j x hjN ⟨t, s, _, f⟩ hi hn
    refine twp_mono (step_twp t hjN s hi) ?_
    intro m' c ⟨t', s', r', h8, h7, f', hc⟩
    refine ⟨⟨t', s', r', fun a ha hc => (f' a ha hc).trans (f a ha hc)⟩, h8, by rw [h7, hn], ?_⟩
    obtain ⟨-, -, hrl, hend, -⟩ := ent_facts hw hjN
    have hnext : (if j + 1 < A.length then (A.getD (j + 1) default).rst else PF + pb.length) =
        A[j].pre + A[j].preLen := by
      by_cases hj1 : j + 1 < A.length
      · simp only [hj1, ↓reduceIte]
        rw [← getD_eq_get hjN]
        exact (hw.contig j hj1).symm
      · simp only [hj1, ↓reduceIte]
        have hl := hw.last
        have : j = A.length - 1 := by omega
        subst this
        rw [getD_eq_get hjN] at hl
        exact hl.symm
    rw [hnext]
    simp only [hjN, ↓reduceIte]
    rw [getD_eq_get hjN]
    omega
  · intro x c ⟨t, s, r, f⟩ _ hc
    refine ⟨t, r rfl, f, ?_⟩
    simp only [hpos, ↓reduceIte] at hc
    rw [getD_eq_get hpos] at hc
    have := (ent_facts hw hpos).2.1
    simp only [PF] at this hc ⊢
    omega

theorem hash_wp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes}
    (h : TrieSt cb pb rs R A K vals m) :
    wp P (Inp pub cb pb) pHash m (fun m' => TrieSt cb pb rs R A K vals m' ∧
      readMem m'.mem C_ROOT 32 = (rootT A K vals).hashOf ∧ HashFrame m m') :=
  wp_of_spec (hash_twp (pub := pub) h) (fun _ _ hq => ⟨hq.1, hq.2.1, hq.2.2.1⟩)

theorem rootIs_wp {m : M} {a : Nat} {d : Bytes} (hk : Base m) (hd : readMem m.mem C_ROOT 32 = d)
    (ha : a + 32 ≤ CELL) :
    wp P (Inp pub cb pb) (pRootIs a) m (fun m' => d = readMem m.mem a 32 ∧ m'.mem = m.mem ∧
      m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  obtain ⟨hk1, hk8, -⟩ := hk
  simp only [CELL, C_ROOT] at ha hd
  simp only [pRootIs]
  npai_auto [hk1, hk8]
  rename_i h
  rw [← hd]; exact h

theorem rootIs_twp {m : M} {a : Nat} {d : Bytes} (hk : Base m) (hd : readMem m.mem C_ROOT 32 = d)
    (ha : a + 32 ≤ CELL) (he : d = readMem m.mem a 32) :
    twp P (Inp pub cb pb) (pRootIs a) m (fun m' c => m'.mem = m.mem ∧ (∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 →
      m'.regs j = m.regs j) ∧ c ≤ 20) := by
  obtain ⟨hk1, hk8, -⟩ := hk
  simp only [CELL, C_ROOT] at ha hd
  simp only [pRootIs]
  npai_auto [hk1, hk8]
  exact ⟨by omega, by rw [hd, he], fun j h0 h1 h2 h3 => by simp [h0, h1, h2, h3]⟩

end

end ReexecNpai
