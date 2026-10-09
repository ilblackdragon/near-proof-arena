import ZkFormal.NearV3.Rcpt.Candidates.DedupTrafficRows
import ZkFormal.NearV3.Rcpt.Candidates.DedupBlockLinks
import ZkFormal.NearV3.Rcpt.Candidates.DedupTrafficBlock

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl SrcpV3
open SrcpProof (regsN regsF regsN_toFp toFp_digMsg ofNat_msgId c16)
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

/-- The candidate root record includes the independently constrained repetition
bit; duplicate roots have no digest receive. SIZE is handled at chain level. -/
theorem root_traffic {s : Nat} (hs : s<tr.height tt) (ht : tr.cell tt s rt=1)
    (B : SrcpB) (rep : Bool)
    (hj : B.j=(tr.cell tt s j).toNat) (hl : B.L=(tr.cell tt s L).toNat)
    (hd : B.dup=decide (tr.cell tt s dup=1)) (hr : B.root=regsN tr tt s)
    (hq : B.qe=(tr.cell tt s qe).toNat) (he : B.le=(tr.cell tt s le).toNat)
    (hp : rep=decide (tr.cell tt s DedupTable.repeated=1))
    (bb : Nat) (hb : bb≠B_SIZE) (sd : Bool) :
    rowTraffic DedupTable.interactions tr tt s pub bb sd =
      (DedupRender.rootMsgs B rep bb sd).map Msg.toFp := by
  have hsg : tr.cell tt s sg=0 := by
    have hh := disjoint hL hs
    rw [ht] at hh
    grind
  have hrep := isBool hL hs (x := DedupTable.repeated) (by simp)
  have hdb := isBool hL hs (x := dup) (by simp [SrcpProof.bools])
  have hgd : tr.cell tt s gD=if tr.cell tt s dup=1 then 0 else 1 := by
    rcases hdb with hd0 | hd1
    · have hc := local_nodup hL hs hd0
      have hwf : tr.cell tt s wf=0 := by
        rcases isBool hL hs (x := wf) (by simp [SrcpProof.bools]) with hw | hw
        · exact hw
        · have hh := (hc.2.2.1 hw).1
          rw [hsg] at hh
          exact False.elim (by simpa using hh)
      rw [hc.2.2.2.2.2.2.2.2.2.1, ht, hwf, hd0]
      simp; grind
    · simp only [hd1, ↓reduceIte]
      exact (duplicate_fields hL hs hd1).2.2.2.2.2.2
  have hc : tr.cell tt s dup=0 →
      tr.cell tt s cId=(K_SRC : Fp)+16*tr.cell tt s qe ∧ tr.cell tt s cLen=tr.cell tt s le := by
    intro hd0
    exact (local_nodup hL hs hd0).2.2.2.2.2.2.2.2.2.2.1 ht
  rw [DedupRender.candidate_rowT, hsg, ht, hgd]
  simp only [show (0 : Fp)≠1 by decide, and_false, ↓reduceIte, List.nil_append,
    and_true, hb, false_and, List.append_nil]
  have mapif (p : Prop) [Decidable p] (xs ys : List Msg) :
      (if p then xs else ys).map Msg.toFp = if p then xs.map Msg.toFp else ys.map Msg.toFp := by
    split <;> rfl
  unfold DedupRender.rootMsgs
  rcases hdb with hdb | hdb <;> rcases hrep with hrep | hrep
  all_goals simp [hd, hp, hdb, hrep, mapif, List.map_append, toFp_digMsg,
    ofNat_msgId, digMsg, hj, hl, hr, hq, he, regsN_toFp, Fp.ofNat_toNat, Msg.toFp,
    hc, c16] <;> rfl

/-- Repetition metadata is extracted from the actual root row, not guessed from
private proof contents. Public SRC balance must bind it to prepared source keys. -/
def repeatedAt (tr : Trace Fp) (tt s : Nat) : Bool :=
  decide (tr.cell tt s DedupTable.repeated=1)

theorem BlockSpan.root_traffic {s n : Nat} {B : SrcpB} (h : BlockSpan tr tt s B n)
    (bb : Nat) (hb : bb≠B_SIZE) (sd : Bool) :
    rowTraffic DedupTable.interactions tr tt s pub bb sd =
      (DedupRender.rootMsgs B (repeatedAt tr tt s) bb sd).map Msg.toFp := by
  cases h with
  | computed m hs ht hd hm =>
    exact DedupProof.root_traffic hL hs ht _ _ rfl rfl rfl rfl rfl rfl rfl bb hb sd
  | skipped hs hd =>
    have hh := duplicate_fields hL hs hd
    apply DedupProof.root_traffic hL hs hh.1 _ _ rfl rfl
    · simp [skipBlock, hd]
    · rfl
    · change (tr.cell tt s q).toNat=(tr.cell tt s qe).toNat
      rw [hh.2.2.2.2.1]
    · change 0=(tr.cell tt s le).toNat
      rw [hh.2.2.2.2.2.1]
      rfl
    · rfl
    · exact hb

theorem BlockSpan.repeated_empty {s n : Nat} {B : SrcpB} (h : BlockSpan tr tt s B n)
    (hp : repeatedAt tr tt s=true) : B.L=12 := by
  have he : tr.cell tt s DedupTable.repeated=1 := by simpa [repeatedAt] using hp
  have hh := (DedupProof.repeated_empty hL (h.start hL).1 he).2
  cases h with
  | computed m hs ht hd hm => change (tr.cell tt s L).toNat=12; rw [hh]; decide +kernel
  | skipped hs hd => exact skip_length hL hs hd

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
