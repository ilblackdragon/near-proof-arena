import ZkFormal.Near.Link.Sha
import ZkFormal.Near.Spec.SoundAccount

/-!
# ZkFormal.Near.Link.EncLemmas — raw encodings vs NEAR encoders (for byte values)
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false

namespace Link

theorem toBytes_append (a b : List Nat) : toBytes (a ++ b) = toBytes a ++ toBytes b := List.map_append

theorem toBytes_cons (x : Nat) (b : List Nat) : toBytes (x :: b) = UInt8.ofNat x :: toBytes b := rfl

theorem bytes8_append {a b : List Nat} : Bytes8 (a ++ b) ↔ Bytes8 a ∧ Bytes8 b := by
  simp only [Bytes8, List.mem_append]
  exact ⟨fun h => ⟨fun y hy => h y (.inl hy), fun y hy => h y (.inr hy)⟩,
    fun h y hy => hy.elim (h.1 y) (h.2 y)⟩

theorem bytes8_of_sub {a b : List Nat} (hb : Bytes8 b) (h : ∀ y ∈ a, y ∈ b) : Bytes8 a :=
  fun y hy => hb y (h y hy)

theorem toBytes_u32r {L : Nat} (h : L < 256) : toBytes (u32r L) = u32 L := by
  simp only [toBytes, u32r, u32, leN, List.map_cons, List.map_nil, List.cons.injEq]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp [UInt8.toNat_ofNat'] <;> omega

theorem toNat_ofNat_byte {x : Nat} (h : x < 256) : (UInt8.ofNat x).toNat = x := by
  rw [UInt8.toNat_ofNat']; omega

theorem map_toNat_toBytes {l : List Nat} (h : Bytes8 l) : (toBytes l).map UInt8.toNat = l := by
  unfold toBytes; rw [List.map_map]
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left; intro x hx; exact toNat_ofNat_byte (h x hx)

theorem leN'_eq (l : List Nat) : leN' l = leNat (toBytes l) := rfl

/-- `leN` of the value of a byte list is the list. -/
theorem leN_leN' {l : List Nat} {w : Nat} (hl : l.length = w) : leN w (leN' l) = toBytes l := by
  rw [leN'_eq, ← hl, ← toBytes_length l]; exact Sound.leN_leNat _

theorem leN'_lt {l : List Nat} {w : Nat} (hl : l.length = w) : leN' l < 256 ^ w := by
  rw [leN'_eq, ← hl, ← toBytes_length l]; exact Sound.leNat_lt _

theorem toBytes_flatMap {α : Type} (f : α → List Nat) :
    ∀ l : List α, toBytes (l.flatMap f) = concatAll (l.map fun a => toBytes (f a))
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, toBytes_append, toBytes_flatMap f l]; rfl

theorem toBytes_map_toNat' (Y : Bytes) : toBytes (Y.map UInt8.toNat) = Y := toBytes_map_toNat Y

theorem toBytes_pubBytes {c : WfClaim} {off w : Nat} {Y : Bytes}
    (h : pubBytes (publicOf c) off w = Y.map UInt8.toNat) : toBytes (pubBytes (publicOf c) off w) = Y := by
  rw [h, toBytes_map_toNat]

theorem map_toNat_inj {a b : Bytes} (h : a.map UInt8.toNat = b.map UInt8.toNat) : a = b := by
  rw [← toBytes_map_toNat a, ← toBytes_map_toNat b, h]

/-! ## Receipts -/

theorem tailN_eq : toBytes tailN = u32 0 ++ u32 0 ++ u32 1 ++ [3] := by decide

theorem toBytes_borshN {l : List Nat} (h : l.length < 256) :
    toBytes (RcptV.borshN l) = borshBytes (toBytes l) := by
  rw [RcptV.borshN, toBytes_append, toBytes_u32r h, borshBytes, toBytes_length]

theorem toBytes_enc {x : RcptV} {r a b c : Nat} (w : x.Wf r a b c) (hb : Bytes8 x.enc) :
    toBytes x.enc = x.toReceipt.encode := by
  obtain ⟨hp, hv, hs⟩ := idLens w
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := w.lens
  have hgp : Bytes8 x.gp := bytes8_of_sub hb (fun y hy => by simp [RcptV.enc, hy])
  have hdep : Bytes8 x.dep := bytes8_of_sub hb (fun y hy => by simp [RcptV.enc, hy])
  have hkt : x.kt < 256 := hb _ (by simp [RcptV.enc])
  simp only [RcptV.enc, toBytes_append, RcptV.toReceipt, Receipt.encode, PublicKey.encode]
  rw [toBytes_borshN (by omega), toBytes_borshN (by omega), toBytes_borshN (by omega), tailN_eq]
  simp only [u128]
  rw [leN_leN' (w := 16) h4, leN_leN' (w := 16) h5]
  have : u8 x.kt = toBytes [x.kt] := by
    simp only [u8, leN, toBytes, List.map_cons, List.map_nil, Nat.mod_eq_of_lt hkt]
  rw [this]
  simp only [List.append_assoc]
  rfl

theorem toReceipt_inSlice {x : RcptV} {r a b c : Nat} (w : x.Wf r a b c) :
    x.toReceipt.inSlice = true := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := w.lens
  obtain ⟨i1, i2, i3, -⟩ := w.ids
  have hgp := leN'_lt (w := 16) h4
  have hdep := leN'_lt (w := 16) h5
  have e : (256 : Nat) ^ 16 = Params.two128 := by decide
  rw [e] at hgp hdep
  simp only [Receipt.inSlice, Receipt.wf, RcptV.toReceipt, PublicKey.wf, i1, i2, i3,
    Bool.and_eq_true, Bool.true_and, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq,
    toBytes_length, h1, Bool.or_eq_true, h2]
  have hns := w.notSystem
  have hnm := w.named
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h3 with h | h <;> simp_all

end Link

end ZkFormal.Near
