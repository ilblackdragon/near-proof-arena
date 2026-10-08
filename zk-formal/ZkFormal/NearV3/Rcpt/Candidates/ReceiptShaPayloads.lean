import ZkFormal.NearV3.Rcpt.Candidates.NativeViewShaRows
import ZkFormal.NearV3.Rcpt.Extract.RcptView

set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 ZkFormal.Near

/-- Exact per-receipt SHA preimages emitted by rSends, excluding the fragmented
RC stream and the public refund body (which is not a SHA job). -/
def receiptShaPayloads (pub : List Algebra.Fp) (x : RcptE) : List (List Nat) :=
  [x.peo,x.leaf]++if x.hr then [x.rid++pubBytes pub PH_HEIGHT 8++List.replicate 8 0] else []

theorem receipt_sha_lengths (pub : List Algebra.Fp) (x : RcptE)
    {r bg tok tok'} (h : x.Wf r bg tok tok') :
    x.enc.length≤347 ∧ x.peo.length≤133 ∧ x.leaf.length=68 ∧
      (x.rid++pubBytes pub PH_HEIGHT 8++List.replicate 8 0).length=48 := by
  have hp : x.p.length≤64 := by
    have hh := h.ids.1
    simp only [AccountId.valid,Bool.and_eq_true,decide_eq_true_eq,toBytes,List.length_map] at hh
    exact hh.1.2
  have hv : x.v.length≤64 := by
    have hh := h.ids.2.1
    simp only [AccountId.valid,Bool.and_eq_true,decide_eq_true_eq,toBytes,List.length_map] at hh
    exact hh.1.2
  have hs : x.s.length≤64 := by
    have hh := h.ids.2.2.1
    simp only [AccountId.valid,Bool.and_eq_true,decide_eq_true_eq,toBytes,List.length_map] at hh
    exact hh.1.2
  have hh := h.lens
  rcases hh with ⟨hrid,hpk,hkt,hgp,hdep,hbef,hlk,hst,haft,hburn,hramt,hrfid,hpeoh,rest⟩
  simp only [RcptV.enc,RcptV.peo,RcptV.leaf,RcptV.borshN,G_LEn,tailN,
    List.length_append,List.length_cons,List.length_nil,u32r,hrid,hpk,hgp,hdep,hburn,
    hrfid,hpeoh,pubBytes,List.length_map,List.length_range,List.length_replicate]
  cases hx : x.hr <;> simp only [hx,Bool.false_eq_true,ite_false,ite_true,List.length_nil,hrfid,and_true] <;> omega

theorem receipt_sha_rows (pub : List Algebra.Fp) (x : RcptE)
    {r bg tok tok'} (h : x.Wf r bg tok tok') :
    hashRows ((receiptShaPayloads pub x).map List.length)≤105 := by
  obtain ⟨_,hp,hl,hr⟩ := receipt_sha_lengths pub x h
  have hpm := ZkFormal.Near.Render.rowsOf_mono hp
  have hp133 : ZkFormal.Near.Render.rowsOf 133=52 := by decide
  have hl68 : ZkFormal.Near.Render.rowsOf 68=35 := by decide
  have hr48 : ZkFormal.Near.Render.rowsOf 48=18 := by decide
  unfold receiptShaPayloads hashRows
  cases hx : x.hr <;>
    simp only [hx,Bool.false_eq_true,ite_false,ite_true,List.append_nil,List.map_cons,
      List.map_nil,List.sum_cons,List.sum_nil,List.cons_append,List.nil_append,hl,hr,hl68,hr48] <;>
    omega

/-- One complete RC preimage per ordered source occurrence, including empty lists. -/
def rcShaPayloads (pub : List Algebra.Fp) (ls : RcptV3Vs) : List (List Nat) :=
  ls.map (fun L => hdrBytes pub L++L.rs.flatMap (fun x => x.enc))

private theorem encoded_receipts_bound (xs : List RcptE)
    (h : ∀x∈xs,x.enc.length≤347) : (xs.flatMap (fun x => x.enc)).length≤347*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hh := ih (fun x hx => h x (by simp [hx]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem rc_list_sha_bound (pub : List Algebra.Fp) (L : ListV3)
    (h : ∀x∈L.rs,x.enc.length≤347) :
    64*ZkFormal.Near.Render.rowsOf (hdrBytes pub L++L.rs.flatMap (fun x => x.enc)).length
      ≤5899*L.rs.length+1492 := by
  have hb := encoded_receipts_bound L.rs h
  have hn : (hdrBytes pub L++L.rs.flatMap (fun x => x.enc)).length=
      12+(L.rs.flatMap (fun x => x.enc)).length := by
    simp [hdrBytes,pubBytes]; omega
  have hh : ∀ n,64*ZkFormal.Near.Render.rowsOf n≤17*n+1288 := by
    intro n
    unfold ZkFormal.Near.Render.rowsOf
    omega
  have hr := hh (hdrBytes pub L++L.rs.flatMap (fun x => x.enc)).length
  rw [hn] at hr ⊢
  omega

theorem rc_batch_sha_bound (pub : List Algebra.Fp) (ls : RcptV3Vs)
    (h : ∀L∈ls,∀x∈L.rs,x.enc.length≤347) :
    64*hashRows ((rcShaPayloads pub ls).map List.length)≤
      5899*(flatR ls).length+1492*ls.length := by
  induction ls with
  | nil => simp [rcShaPayloads,hashRows,flatR]
  | cons L ls ih =>
    have hl := rc_list_sha_bound pub L (h L (by simp))
    have hi := ih (fun L hl => h L (by simp [hl]))
    simp only [rcShaPayloads,hashRows,List.map_cons,List.sum_cons,flatR,List.flatMap_cons,
      List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one] at *
    omega

theorem receipt_batch_sha_bound (pub : List Algebra.Fp) (xs : List RcptE)
    (h : ∀x∈xs,∃r bg tok tok',x.Wf r bg tok tok') :
    hashRows ((xs.flatMap (receiptShaPayloads pub)).map List.length)≤105*xs.length := by
  induction xs with
  | nil => simp [hashRows]
  | cons x xs ih =>
    obtain ⟨r,bg,tok,tok',hx⟩ := h x (by simp)
    have hp := receipt_sha_rows pub x hx
    have hi := ih (fun x hx => h x (by simp [hx]))
    simp only [List.flatMap_cons,List.map_append,hashRows,List.sum_append,
      List.length_cons,Nat.mul_add,Nat.mul_one] at *
    omega

/-- Retain the exact encoded receipt byte charge for joint witness budgeting. -/
def receiptEncodedBytes (ls : RcptV3Vs) : Nat :=
  ((flatR ls).flatMap (fun x => x.enc)).length

theorem rc_payload_byte_bound (pub : List Algebra.Fp) (ls : RcptV3Vs) :
    64*hashRows ((rcShaPayloads pub ls).map List.length)≤
      17*receiptEncodedBytes ls+1492*ls.length := by
  induction ls with
  | nil => simp [rcShaPayloads,hashRows,receiptEncodedBytes,flatR]
  | cons L ls ih =>
    have hh : ∀ n,64*ZkFormal.Near.Render.rowsOf n≤17*n+1288 := by
      intro n
      unfold ZkFormal.Near.Render.rowsOf
      omega
    have hn : (hdrBytes pub L++L.rs.flatMap (fun x => x.enc)).length=
        12+(L.rs.flatMap (fun x => x.enc)).length := by
      simp [hdrBytes,pubBytes]; omega
    have hr := hh (hdrBytes pub L++L.rs.flatMap (fun x => x.enc)).length
    simp only [rcShaPayloads,hashRows,List.map_cons,List.sum_cons,receiptEncodedBytes,
      flatR,List.flatMap_cons,List.flatMap_append,List.length_append,List.length_cons,
      Nat.mul_add,Nat.mul_one,hn] at *
    omega

theorem receipt_payload_byte_bound (pub : List Algebra.Fp) (ls : RcptV3Vs)
    (h : ∀x∈flatR ls,∃r bg tok tok',x.Wf r bg tok tok') :
    64*(hashRows ((rcShaPayloads pub ls).map List.length)+
      hashRows (((flatR ls).flatMap (receiptShaPayloads pub)).map List.length))≤
        17*receiptEncodedBytes ls+6720*(flatR ls).length+1492*ls.length := by
  have hr := rc_payload_byte_bound pub ls
  have hp := receipt_batch_sha_bound pub (flatR ls) h
  omega

end ZkFormal.NearV3.Rcpt.Candidates
