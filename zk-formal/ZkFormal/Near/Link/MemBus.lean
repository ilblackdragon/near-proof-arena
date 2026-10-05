import ZkFormal.Near.Link.EncLemmas
import ZkFormal.Near.Spec.SoundShape

/-!
# ZkFormal.Near.Link.MemBus — the `MEM` bus as a permutation of natural messages

Writes `W` (receipt writes `(k, r+1, i, aft, lk, st)`, acct initial writes
`(k, 0, i, pre lanes)`) and reads `R` (receipt reads `(k, tprev, i, bef, lk, st)`,
acct final reads `(k, tlast, i, post lanes)`) are canonical, `W` has distinct
keys `(k, t, i)`, and `W ~ R` as lists of naturals.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

/-! ## From images to naturals -/

theorem count_toFp : ∀ {l : List Msg}, (∀ y ∈ l, Canon y) → ∀ {x : Msg}, Canon x →
    (l.map Msg.toFp).count x.toFp = l.count x
  | [], _, _, _ => rfl
  | y :: l, hl, x, hx => by
    rw [List.map_cons, List.count_cons, List.count_cons,
      count_toFp (fun z hz => hl z (List.mem_cons_of_mem _ hz)) hx]
    congr 1
    by_cases hyx : y = x
    · subst hyx; simp
    · have : y.toFp ≠ x.toFp := fun he => hyx (toFp_inj (hl y List.mem_cons_self) hx he)
      simp [hyx, this]

theorem perm_nat {W R : List Msg} (hW : ∀ y ∈ W, Canon y) (hR : ∀ y ∈ R, Canon y)
    (hp : (W.map Msg.toFp).Perm (R.map Msg.toFp)) : W.Perm R := by
  rw [List.perm_iff_count]; intro x
  by_cases hx : Canon x
  · rw [← count_toFp hW hx, ← count_toFp hR hx]; exact List.perm_iff_count.mp hp _
  · have h1 : x ∉ W := fun hm => hx (hW x hm)
    have h2 : x ∉ R := fun hm => hx (hR x hm)
    rw [List.count_eq_zero.mpr h1, List.count_eq_zero.mpr h2]

/-! ## Messages -/

def wrMsg (x : RcptV) (r i : Nat) : Msg :=
  [x.kslot, r + 1, i, x.aft.getD i 0, x.lk.getD i 0, x.st.getD i 0]
def rdMsg (x : RcptV) (i : Nat) : Msg :=
  [x.kslot, x.tprev, i, x.bef.getD i 0, x.lk.getD i 0, x.st.getD i 0]
def awMsg (a : AcctV) (i : Nat) : Msg := [a.k, 0, i] ++ acctLane a a.pre i
def arMsg (a : AcctV) (i : Nat) : Msg := [a.k, a.tlast, i] ++ acctLane a a.post i

theorem rcptSends_mem (pub : List Fp) (rs : RcptVs) :
    rcptSends pub rs B_MEM =
      (rs.zip (List.range rs.length)).flatMap fun p => (List.range 16).map (wrMsg p.1 p.2 ·) := by
  simp [rcptSends, B_MEM, B_BYTES, B_KEYNIB]; rfl

theorem rcptRecvs_mem (pub : List Fp) (rs : RcptVs) :
    rcptRecvs pub rs B_MEM =
      (rs.zip (List.range rs.length)).flatMap fun p => (List.range 16).map (rdMsg p.1 ·) := by
  simp [rcptRecvs, B_MEM, B_DIGEST, B_FINAL]; rfl

theorem acctSends_mem (as : List AcctV) :
    acctSends as B_MEM = as.flatMap fun a => (List.range 16).map (awMsg a ·) := by
  simp [acctSends, B_MEM, B_BYTES]; rfl

theorem acctRecvs_mem (as : List AcctV) :
    acctRecvs as B_MEM = as.flatMap fun a => (List.range 16).map (arMsg a ·) := by
  simp [acctRecvs, B_MEM]; rfl

/-- Lists of natural messages on `MEM`. -/
def memW (pub : List Fp) (rs : RcptVs) (as : List AcctV) : List Msg :=
  rcptSends pub rs B_MEM ++ acctSends as B_MEM
def memR (pub : List Fp) (rs : RcptVs) (as : List AcctV) : List Msg :=
  rcptRecvs pub rs B_MEM ++ acctRecvs as B_MEM

theorem mem_memW {pub : List Fp} {rs : RcptVs} {as : List AcctV} {m : Msg} :
    m ∈ memW pub rs as ↔ (∃ r, ∃ hr : r < rs.length, ∃ i, i < 16 ∧ m = wrMsg rs[r] r i) ∨
      (∃ a ∈ as, ∃ i, i < 16 ∧ m = awMsg a i) := by
  simp only [memW, List.mem_append, rcptSends_mem, acctSends_mem, List.mem_flatMap, List.mem_map,
    List.mem_range]
  constructor
  · rintro (⟨⟨x, r⟩, hp, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩)
    · obtain ⟨hr, rfl⟩ := mem_zip_range.mp hp; exact .inl ⟨r, hr, i, hi, rfl⟩
    · exact .inr ⟨a, ha, i, hi, rfl⟩
  · rintro (⟨r, hr, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩)
    · exact .inl ⟨(rs[r], r), mem_zip_range.mpr ⟨hr, rfl⟩, i, hi, rfl⟩
    · exact .inr ⟨a, ha, i, hi, rfl⟩

theorem rd_mem_memR {pub : List Fp} {rs : RcptVs} {as : List AcctV} {r : Nat} (hr : r < rs.length)
    {i : Nat} (hi : i < 16) : rdMsg rs[r] i ∈ memR pub rs as := by
  simp only [memR, List.mem_append, rcptRecvs_mem, List.mem_flatMap, List.mem_map, List.mem_range]
  exact .inl ⟨(rs[r], r), mem_zip_range.mpr ⟨hr, rfl⟩, i, hi, rfl⟩

theorem ar_mem_memR {pub : List Fp} {rs : RcptVs} {as : List AcctV} {a : AcctV} (ha : a ∈ as)
    {i : Nat} (hi : i < 16) : arMsg a i ∈ memR pub rs as := by
  simp only [memR, List.mem_append, acctRecvs_mem, List.mem_flatMap, List.mem_map, List.mem_range]
  exact .inr ⟨a, ha, i, hi, rfl⟩

theorem mem_memR {pub : List Fp} {rs : RcptVs} {as : List AcctV} {m : Msg} :
    m ∈ memR pub rs as → (∃ r, ∃ hr : r < rs.length, ∃ i, i < 16 ∧ m = rdMsg rs[r] i) ∨
      (∃ a ∈ as, ∃ i, i < 16 ∧ m = arMsg a i) := by
  simp only [memR, List.mem_append, rcptRecvs_mem, acctRecvs_mem, List.mem_flatMap, List.mem_map,
    List.mem_range]
  rintro (⟨⟨x, r⟩, hp, i, hi, rfl⟩ | ⟨a, ha, i, hi, rfl⟩)
  · obtain ⟨hr, rfl⟩ := mem_zip_range.mp hp; exact .inl ⟨r, hr, i, hi, rfl⟩
  · exact .inr ⟨a, ha, i, hi, rfl⟩

/-! ## Nodup of the writes -/

theorem nodup_range_map {α : Type} (f : Nat → α) (hf : ∀ i j, f i = f j → i = j) (n : Nat) :
    ((List.range n).map f).Nodup :=
  nodup_map_of_inj_on (fun a _ b _ h => hf a b h) List.nodup_range

theorem memW_nodup (pub : List Fp) (rs : RcptVs) (as : List AcctV)
    (hk : (as.map (·.k)).Nodup) : (memW pub rs as).Nodup := by
  unfold memW; rw [rcptSends_mem, acctSends_mem, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · apply Sound.nodup_flatMap_of
    · intro p _; exact nodup_range_map _ (fun i j h => by simp [wrMsg] at h; exact h.1) 16
    · intro i j a b x hij ha hb hxa hxb
      simp only [List.mem_map, List.mem_range] at hxa hxb
      obtain ⟨i1, -, rfl⟩ := hxa
      obtain ⟨i2, -, he⟩ := hxb
      have h1 := List.mem_of_getElem? ha
      have h2 := List.mem_of_getElem? hb
      obtain ⟨-, hra⟩ := mem_zip_range.mp (show (a.1, a.2) ∈ _ from h1)
      obtain ⟨-, hrb⟩ := mem_zip_range.mp (show (b.1, b.2) ∈ _ from h2)
      simp only [wrMsg, List.cons.injEq] at he
      have hab : a.2 = b.2 := by omega
      -- positions `i`, `j` of `zip … range` have second components `i`, `j`
      have hi := (List.getElem?_eq_some_iff.mp ha)
      have hj := (List.getElem?_eq_some_iff.mp hb)
      obtain ⟨hi1, hi2⟩ := hi; obtain ⟨hj1, hj2⟩ := hj
      have e1 : a.2 = i := by rw [← hi2, List.getElem_zip]; simp
      have e2 : b.2 = j := by rw [← hj2, List.getElem_zip]; simp
      exact hij (by omega)
  · apply Sound.nodup_flatMap_of
    · intro a _; exact nodup_range_map _ (fun i j h => by simp [awMsg] at h; exact h.1) 16
    · intro i j a b x hij ha hb hxa hxb
      simp only [List.mem_map, List.mem_range] at hxa hxb
      obtain ⟨i1, -, rfl⟩ := hxa
      obtain ⟨i2, -, he⟩ := hxb
      simp only [awMsg, List.cons_append, List.cons.injEq] at he
      have hl : (as.map (·.k))[i]? = some a.k := by simp [ha]
      have hl' : (as.map (·.k))[j]? = some b.k := by simp [hb]
      have hlen : i < (as.map (·.k)).length := by
        simp only [List.length_map]; exact (List.getElem?_eq_some_iff.mp ha).1
      exact hij ((List.Nodup.getElem?_inj hlen hk).mp (by rw [hl, hl', he.1]))
  · intro x hx y hy hxy
    subst hxy
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hx hy
    obtain ⟨p, -, i, -, rfl⟩ := hx
    obtain ⟨a, -, j, -, he⟩ := hy
    simp [wrMsg, awMsg] at he

end Link

end ZkFormal.Near
