import ZkFormal.NearV3.Rcpt.Candidates.SizeCountSourceBounds
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountNodeSender

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

private theorem filter_sum_le {α : Type} (xs : List α) (p : α → Bool) (f : α → Nat) :
    ((xs.filter p).map f).sum≤(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => cases hp : p a <;> simp [hp] <;> omega

theorem node_charge_bounds {vs : List NodeS3} (h : NodeWf3 vs) :
    nodePayload vs≤2^22 ∧ (vs.filter fun v => !v.dup).length≤2^22 := by
  have hp := filter_sum_le vs (fun v => !v.dup) (fun v => (v.v.ser false).length)
  have hr := h.rows
  have hc := List.length_filter_le (fun v => !v.dup) vs
  have hn := h.count
  unfold nodePayload
  omega

theorem val_charge_bounds {es : List ValE} (h : ValWf es) :
    valPayload es≤2^22 ∧ (es.filter fun v => !v.dup).length≤2^22 := by
  have hp : valPayload es≤(es.map fun e => if e.vz then 1 else e.len).sum := by
    unfold valPayload
    clear h
    induction es with
    | nil => simp
    | cons e es ih =>
      cases hz : e.vz <;> cases hd : e.dup <;> simp [hz,hd] <;> omega
  have hc : es.length≤(es.map fun e => if e.vz then 1 else e.len).sum := by
    have hw : ∀ e∈es,1≤(if e.vz then 1 else e.len) := by
      intro e he
      cases hz : e.vz
      · have hh := (h.shape e he).2 hz
        simp [hz]; omega
      · simp [hz]
    clear hp h
    induction es with
    | nil => simp
    | cons e es ih =>
      have hh := hw e (by simp)
      have ht := ih (fun x hx => hw x (by simp [hx]))
      simp only [List.length_cons,List.map_cons,List.sum_cons]
      omega
  have hr := h.rows
  have hf := List.length_filter_le (fun v => !v.dup) es
  omega

theorem source_charge_cap
    {src rcpt : Trace Fp} {ts tr : Nat} {pub : List Fp}
    (hsrc : TableLocal (DedupTable.table 24) src ts pub)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    {bs : List SrcpB} {se : Nat} (hs : DedupProof.BlockChain src ts 0 bs se)
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hbalance : ∀ m : List Fp,
      ((List.range (src.height ts)).flatMap (fun q => rowTraffic DedupTable.interactions src ts q pub B_RCL false)).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m) :
    (bs.map fun B => B.L+33*B.path.length).sum≤2^24+2^22 := by
  have hb := source_charge_bound hsrc hrcpt hs hr hbalance
  have hsH : src.height ts≤2^24 := Nat.pow_le_pow_right (by decide) hsrc.log_le
  have hrH := RcptV3Proof.height_le hrcpt
  omega

/-- Physical row caps, not the SIZE inequality being proved, rule out modular
wraparound. Only the public fixed-overhead admission bound remains external. -/
theorem totals_no_wrap {vs : List NodeS3} {es : List ValE}
    (hn : NodeWf3 vs) (hv : ValWf es) (sourceSize overhead : Nat)
    (hs : sourceSize≤2^24+2^22) (ho : overhead≤8388608) :
    overhead+nodePayload vs+valPayload es+sourceSize+
      4*((vs.filter fun v => !v.dup).length+(es.filter fun v => !v.dup).length)+2^24≤P := by
  obtain ⟨hnp,hnc⟩ := node_charge_bounds hn
  obtain ⟨hvp,hvc⟩ := val_charge_bounds hv
  unfold P
  omega

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
