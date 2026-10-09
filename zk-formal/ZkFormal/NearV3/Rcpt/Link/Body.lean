import ZkFormal.NearV3.Rcpt.Extract.RcptView
import ZkFormal.Near.Extract.Eval
import ZkFormal.Near.Extract.Statements

/-!
# ZkFormal.NearV3.Rcpt.Link.Body — the refund body is the public body `B`

`rcptV3` sends the refund bytes as `BYTES (K_RF, 8 + k, s_k)` (`k < m`); the public bus
receives `(K_RF, 8 + k, B_k)` (`k < |B| − 8`) on the same bus; every other `BYTES` sender uses
ids of other kinds; SHA may receive anything.  With `m = |B| − 8` (the table's `o2End = |B|`):

* `body_eq`: the stream is `B[8 …]`;
* `body_sha0`: SHA receives no kind-2 message (so `ShaHyp`'s `others` may omit the body).
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- The balance on `BYTES` for one message: `stream + others = SHA + public`. -/
structure BodyBal (s Bb : List Nat) (others : List Msg) (shaR : List Fp → Nat) : Prop where
  bal : ∀ m, cnt (emitAt K_RF 8 s ++ others) m = shaR m + cnt (emitAt K_RF 8 Bb) m
  others_id : ∀ x ∈ others, ∀ a, x.head? = some a → a < P ∧ a ≠ K_RF
  len : s.length = Bb.length
  small : 8 + s.length < P ∧ (∀ y ∈ s, y < P) ∧ ∀ y ∈ Bb, y < P

theorem mem_emitAt' {id off : Nat} {bs : List Nat} {m : Msg} :
    m ∈ emitAt id off bs ↔ ∃ i, i < bs.length ∧ m = [id, off + i, bs.getD i 0] := by
  simp only [emitAt, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem kRF_lt : K_RF < P := by unfold K_RF P; omega

/-- **The refund stream is `B[8 …]`.** -/
theorem body_eq {s Bb : List Nat} {others : List Msg} {shaR : List Fp → Nat}
    (H : BodyBal s Bb others shaR) : s = Bb := by
  apply List.ext_getElem H.len
  intro k hk hk'
  -- the public message at position 8 + k is sent by someone: the stream (other ids differ)
  have hm : Msg.toFp [K_RF, 8 + k, Bb[k]] ∈ (emitAt K_RF 8 Bb).map Msg.toFp :=
    List.mem_map.mpr ⟨_, mem_emitAt'.mpr ⟨k, hk', by simp [List.getD_eq_getElem?_getD, hk']⟩, rfl⟩
  have hpos : 0 < cnt (emitAt K_RF 8 s ++ others) (Msg.toFp [K_RF, 8 + k, Bb[k]]) := by
    rw [H.bal]; have := List.count_pos_iff.mpr hm; unfold cnt; omega
  unfold cnt at hpos
  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp (List.count_pos_iff.mp hpos)
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨i, hi, rfl⟩ := mem_emitAt'.mp hx
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq] at hxe
    obtain ⟨-, e1, e2, -⟩ := hxe
    have hik : i = k := by
      have := ofNat_inj (a := 8 + i) (b := 8 + k) (by have := H.small.1; omega) (by have := H.small.1; omega)
        (by simpa [natCast_eq] using e1)
      omega
    subst hik
    have hs : s.getD i 0 = s[i] := by simp [List.getD_eq_getElem?_getD, hk]
    rw [hs] at e2
    exact ofNat_inj (H.small.2.1 _ (List.getElem_mem hk)) (H.small.2.2 _ (List.getElem_mem hk'))
      (by simpa [natCast_eq] using e2)
  · exfalso
    obtain ⟨hlt, hne⟩ := H.others_id x hx (x.headD 0) (by
      cases x with
      | nil => simp [Msg.toFp] at hxe
      | cons a l => rfl)
    cases x with
    | nil => simp [Msg.toFp] at hxe
    | cons a l =>
      simp only [Msg.toFp, List.map_cons, List.cons.injEq] at hxe
      exact hne (ofNat_inj hlt kRF_lt (by simpa [natCast_eq] using hxe.1))

/-- **SHA receives no body message.** -/
theorem body_sha0 {s Bb : List Nat} {others : List Msg} {shaR : List Fp → Nat}
    (H : BodyBal s Bb others shaR) (m : List Fp) (hm : m.head? = some (Fp.ofNat K_RF)) : shaR m = 0 := by
  have hb := H.bal m
  rw [body_eq H] at hb
  have h0 : cnt others m = 0 := by
    unfold cnt
    apply List.count_eq_zero.mpr
    intro hmem
    obtain ⟨x, hxo, rfl⟩ := List.mem_map.mp hmem
    cases x with
    | nil => simp [Msg.toFp] at hm
    | cons a l =>
      obtain ⟨hlt, hne⟩ := H.others_id (a :: l) hxo a rfl
      simp only [Msg.toFp, List.map_cons, List.head?_cons, Option.some.injEq] at hm
      exact hne (ofNat_inj hlt kRF_lt (by simpa [natCast_eq] using hm))
  unfold cnt at hb h0
  rw [List.map_append, List.count_append] at hb
  omega

end ZkFormal.NearV3
