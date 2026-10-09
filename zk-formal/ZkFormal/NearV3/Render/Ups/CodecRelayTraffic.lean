import ZkFormal.NearV3.Render.Ups.CodecRelayValue
import ZkFormal.Near.Extract.BusCount
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Sched
/-- Actual row traffic: the fresh-state relay precedes the unchanged sanity
hash bytes. This preserves all multiplicities, even before assuming constraints. -/
theorem codecRelay_rowBytes (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic codecTable.interactions tr t r pub B_BYTES true =
    (rowTraffic Codec.interactions tr t r pub B_SPOST true).map relayMsg ++
      rowTraffic Codec.interactions tr t r pub B_BYTES true := by
  simp only [codecTable,Codec.table,Codec.interactions,List.set_cons_zero,List.set_cons_succ,
    rowTraffic,List.flatMap_cons,List.flatMap_nil,relay]
  simp only [B_BYTES,B_SPOST,B_VBYTES,B_DIGEST,B_S0F,B_SPLEN,B_SPAR,B_SDL,B_SPUBB,
    B_SOP,B_SFIN,B_SDG,B_SA0,B_SCMP]
  simp only [reduceCtorEq, Bool.false_eq_true, and_self, and_false, and_true, false_and,
    true_and, ite_true, ite_false, List.nil_append, List.append_nil, List.map_replicate]
  simp only [Sched.B_SPOST,Sched.B_SPLEN]
  simp
  exact ⟨rfl,Or.inr (relay_message tr t r pub)⟩
/-- The actual full-table fresh relay inventory, including every physical row. -/
def codecRelayMsgs (tr : Trace Fp) (t : Nat) (pub : List Fp) : List (List Fp) :=
  ((List.range (tr.height t)).flatMap fun r =>
    rowTraffic Codec.interactions tr t r pub B_SPOST true).map relayMsg

/-- Exact complete BYTES inventory: fresh state bytes plus the unchanged
scheduler sanity-hash bytes; no omitted rows or allocation premise. -/
theorem codecRelay_tableBytes (tr : Trace Fp) (t : Nat) (pub : List Fp) (m : List Fp) :
    tableBusCount codecTable.interactions tr t pub B_BYTES true m =
      (codecRelayMsgs tr t pub).count m +
      tableBusCount Codec.interactions tr t pub B_BYTES true m := by
  rw [tableBusCount_eq,tableBusCount_eq]
  unfold codecRelayMsgs
  rw [List.map_flatMap]
  generalize List.range (tr.height t) = rs
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.flatMap_cons,codecRelay_rowBytes,List.count_append] at ih ⊢
    omega

/-- Old SPOST sends disappear completely, so no dangling fresh-value lookup
remains after removing the compact UPS value rows. -/
theorem codecRelay_noSpost (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic codecTable.interactions tr t r pub B_SPOST true = [] := by
  simp [codecTable,Codec.table,Codec.interactions,rowTraffic,relay,
    B_SPOST,Sched.B_SPOST,B_BYTES,B_VBYTES,B_DIGEST,B_S0F,B_SPLEN,Sched.B_SPLEN,
    B_SPAR,B_SDL,B_SPUBB,B_SOP,B_SFIN,B_SDG,B_SA0,B_SCMP]
theorem codecRelay_rowRecvs (tr : Trace Fp) (t r : Nat) (pub : List Fp) (b : Nat) :
    rowTraffic codecTable.interactions tr t r pub b false =
      rowTraffic Codec.interactions tr t r pub b false := by
  simp [codecTable,Codec.table,Codec.interactions,rowTraffic,relay]

theorem codecRelay_rowOther (tr : Trace Fp) (t r : Nat) (pub : List Fp) {b : Nat}
    (hb : B_BYTES≠b) (hs : B_SPOST≠b) :
    rowTraffic codecTable.interactions tr t r pub b true =
      rowTraffic Codec.interactions tr t r pub b true := by
  have hs' : Sched.B_SPOST≠b := hs
  simp [codecTable,Codec.table,Codec.interactions,rowTraffic,relay,hb,hs']
end ZkFormal.NearV3.Render.UpsRelay
