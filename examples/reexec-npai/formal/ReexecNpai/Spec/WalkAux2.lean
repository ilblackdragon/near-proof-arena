import ReexecNpai.Spec.State
import ReexecNpai.Spec.WalkAux

/-!
# Helper lemmas for `Spec/Walk.lean`: what the walk reads from the trie section
-/

set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1 WalkProof WalkAux

namespace WalkAux

theorem nleN_eq : ∀ (w x : Nat), NearSpec.leN w x = ArenaCore.Bytes.leN w x
  | 0, _ => rfl
  | w + 1, x => by simp only [NearSpec.leN, ArenaCore.Bytes.leN, nleN_eq w (x / 256)]

theorem leToNat_u32 (x : Nat) (h : x < 4294967296) : ArenaCore.Bytes.leToNat (u32 x) = x := by
  rw [u32, nleN_eq, leToNat_leN 4 x (by simpa using h)]

theorem leToNat_u16 (x : Nat) (h : x < 65536) : ArenaCore.Bytes.leToNat (u16 x) = x := by
  rw [u16, nleN_eq, leToNat_leN 2 x (by simpa using h)]

theorem readMem_mid {M0 : Nat → UInt8} {a n : Nat} {l : List UInt8} (h : readMem M0 a n = l) (i k : Nat)
    (hk : i + k ≤ n) : readMem M0 (a + i) k = (l.drop i).take k := by
  subst h
  apply List.ext_getElem (by simp; omega)
  intro q h1 h2
  simp [readMem, Nat.add_assoc]

theorem getD_of' {A : List Ent} {j : Nat} {e : Ent} (h : A[j]? = some e) (hl : j < A.length) : A[j] = e := by
  rw [List.getElem?_eq_getElem hl] at h; exact Option.some.inj h

theorem lt_of_get {A : List Ent} {j : Nat} {e : Ent} (h : A[j]? = some e) : j < A.length := by
  rcases Nat.lt_or_ge j A.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none h'] at h; cases h

section
variable {cb pb : Bytes} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes} {m : M}

/-- Layout facts of entry `j`'s record. -/
theorem ent_bounds (h : TrieSt cb pb rs R A K vals m) {j : Nat} {e : Ent} (hj : A[j]? = some e) :
    PF < e.pre ∧ e.pre + e.preLen ≤ 13844304 ∧ NFOk e.nf ∧
    (∃ z zs, readMem m.mem e.pre e.preLen = preImg e.nf (vlenAt pb e) z zs) ∧
    (e.val ≠ 0 → hasVal e.nf = true) ∧
    (match e.nf with
     | .ext _ hh _ => pseg pb (e.pre - 1) 1 = [if hh.isNone then 1 else 0]
     | .branch _ ks _ => pseg pb (e.pre - 2) 2 = u16 (bitsRev ks 0)
     | _ => True) := by
  have hl := lt_of_get hj
  obtain ⟨e', he', hok, h1, h2, h3, -, hv, hhd, -⟩ := h.tok.wf.nodes j hl
  rw [hj] at he'; cases he'
  obtain ⟨z, zs, -, -, -, hpm⟩ := h.tmem.pmem j hl
  rw [getD_of' hj hl] at hpm
  have hpl := h.plen
  simp only [PF, PMAX] at h1 h2 h3 hpl ⊢
  refine ⟨by omega, by omega, hok, ⟨z, zs, hpm⟩, ?_, hhd⟩
  intro hv0
  by_cases hh : hasVal e.nf = true
  · exact hh
  · rw [ite_neg hh] at hv; exact absurd hv hv0

theorem u32_len (x : Nat) : (u32 x).length = 4 := by simp [u32, NearSpec.leN]

theorem nibs_of_ok {k : List Nat} (h : nibblesOk k = true) : ∀ x ∈ k, x < 16 := by
  simpa [nibblesOk] using h

/-- What the walk reads from a leaf / extension record (`tag ‖ u32 hl ‖ hp ‖ …`). -/
theorem kh_hdr (h : TrieSt cb pb rs R A K vals m) {j : Nat} {e : Ent} (hj : A[j]? = some e)
    {k : List Nat} {lf : Bool} {tag : UInt8}
    (hpi : ∀ z zs, ∃ rest, preImg e.nf (vlenAt pb e) z zs = [tag] ++ u32 (hexPrefix k lf).length ++ hexPrefix k lf ++ rest) :
    m.mem e.pre = tag ∧ ArenaCore.Bytes.leToNat (readMem m.mem (e.pre + 1) 4) = (hexPrefix k lf).length ∧
    readMem m.mem (e.pre + 5) (hexPrefix k lf).length = hexPrefix k lf ∧
    e.pre + 5 + (hexPrefix k lf).length ≤ 13844304 ∧ PF < e.pre ∧ (hexPrefix k lf).length < 4294967296 := by
  obtain ⟨hpf, hend, -, ⟨z, zs, hpm⟩, -, -⟩ := ent_bounds h hj
  obtain ⟨rest, hr⟩ := hpi z zs
  rw [hr] at hpm
  have hlen := congrArg List.length hpm
  simp only [readMem_length, List.length_append, List.length_singleton, u32_len] at hlen
  have hl1 : (hexPrefix k lf).length = 1 + k.length / 2 := hexPrefix_len k lf
  have hlt : (hexPrefix k lf).length < 4294967296 := by
    have := hexPrefix_len k lf; simp only [PF] at hpf; omega
  refine ⟨?_, ?_, ?_, by omega, hpf, hlt⟩
  · have := readMem_mid hpm 0 1 (by omega)
    simp [readMem] at this; exact this
  · rw [readMem_mid hpm 1 4 (by omega)]
    simp only [List.singleton_append, List.cons_append, List.nil_append, List.drop_one, List.tail_cons, List.append_assoc]
    rw [List.take_left' (u32_len _), leToNat_u32 _ hlt]
  · rw [readMem_mid hpm 5 _ (by omega)]
    simp only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc]
    rw [show 5 = 4 + 1 by rfl, List.drop_succ_cons, List.drop_left' (u32_len _), List.take_left' rfl]

theorem leaf_hdr (h : TrieSt cb pb rs R A K vals m) {j : Nat} {e : Ent} (hj : A[j]? = some e)
    {k : List Nat} {ref : Option (Nat × Bytes)} {mm : Nat} (hn : e.nf = .leaf k ref mm) :
    (m.mem e.pre).toNat = 0 ∧ ArenaCore.Bytes.leToNat (readMem m.mem (e.pre + 1) 4) = (hexPrefix k true).length ∧
    readMem m.mem (e.pre + 5) (hexPrefix k true).length = hexPrefix k true ∧
    e.pre + 5 + (hexPrefix k true).length ≤ 13844304 ∧ PF < e.pre ∧ (∀ x ∈ k, x < 16) := by
  have hok : nibblesOk k = true := by
    have := (ent_bounds h hj).2.2.1; rw [hn] at this; exact this.1
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := kh_hdr h hj (k := k) (lf := true) (tag := 0) (by
    intro z zs; rw [hn]; simp only [preImg, List.append_assoc]; exact ⟨_, rfl⟩)
  exact ⟨by rw [h1]; rfl, h2, h3, h4, h5, nibs_of_ok hok⟩

theorem ext_hdr (h : TrieSt cb pb rs R A K vals m) {j : Nat} {e : Ent} (hj : A[j]? = some e)
    {k : List Nat} {hh : Option Bytes} {mm : Nat} (hn : e.nf = .ext k hh mm) :
    (m.mem e.pre).toNat = 3 ∧ ArenaCore.Bytes.leToNat (readMem m.mem (e.pre + 1) 4) = (hexPrefix k false).length ∧
    readMem m.mem (e.pre + 5) (hexPrefix k false).length = hexPrefix k false ∧
    e.pre + 5 + (hexPrefix k false).length ≤ 13844304 ∧ PF < e.pre ∧ (∀ x ∈ k, x < 16) ∧
    (m.mem (e.pre - 1)).toNat = (if hh.isNone then 1 else 0) := by
  obtain ⟨-, -, hok, -, -, hhd⟩ := ent_bounds h hj
  rw [hn] at hok hhd
  have hm := h.tmem.hmem j (lt_of_get hj)
  rw [getD_of' hj (lt_of_get hj), hn] at hm
  simp only at hm
  rw [hhd] at hm
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := kh_hdr h hj (k := k) (lf := false) (tag := 3) (by
    intro z zs; rw [hn]; simp only [preImg, List.append_assoc]; exact ⟨_, rfl⟩)
  refine ⟨by rw [h1]; rfl, h2, h3, h4, h5, nibs_of_ok hok.1, ?_⟩
  simp only [readMem, List.range, List.range.loop, List.map, Nat.add_zero, List.cons.injEq, and_true] at hm
  rw [hm]; split <;> rfl

theorem br_hdr (h : TrieSt cb pb rs R A K vals m) {j : Nat} {e : Ent} (hj : A[j]? = some e)
    {v : Option (Option (Nat × Bytes))} {ks : List (Option (Option Bytes))} {mm : Nat} (hn : e.nf = .branch v ks mm) :
    ((m.mem e.pre).toNat = 1 ∨ (m.mem e.pre).toNat = 2) ∧ ks.length = 16 ∧
    ArenaCore.Bytes.leToNat (readMem m.mem (e.pre - 2) 2) = bitsRev ks 0 ∧ PF < e.pre ∧
    e.pre ≤ 13844304 := by
  obtain ⟨hpf, hend, hok, ⟨z, zs, hpm⟩, -, hhd⟩ := ent_bounds h hj
  rw [hn] at hok hhd
  have hm := h.tmem.hmem j (lt_of_get hj)
  rw [getD_of' hj (lt_of_get hj), hn] at hm
  simp only at hm
  rw [hhd] at hm
  have hlen : ks.length = 16 := hok.1
  refine ⟨?_, hlen, ?_, hpf, by omega⟩
  · rw [hn] at hpm
    have hpl := congrArg List.length hpm
    have h0 := readMem_mid hpm 0 1 (by
      rw [readMem_length] at hpl; rw [hpl]; simp only [preImg, List.length_append]
      rcases v with _ | _ | ⟨_, _⟩ <;> simp <;> omega)
    simp only [Nat.add_zero, List.drop_zero, readMem, List.range, List.range.loop, List.map] at h0
    rcases v with _ | _ | ⟨_, _⟩ <;> simp [preImg] at h0 <;> rw [h0] <;> simp
  · rw [hm, leToNat_u16 _ (by have := bitsRev_lt ks; rw [hlen] at this; simpa using this)]

end

end WalkAux

end ReexecNpai
