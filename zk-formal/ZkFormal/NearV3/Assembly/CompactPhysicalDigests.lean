import ZkFormal.NearV3.Candidates.CompactHeight
import ZkFormal.NearV3.Render.Ups.CompactExtract.TableTraffic
import ZkFormal.NearV3.Render.Ups.RelayNativeInventory

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render Render.UpsGen Render.UpsRelay UpsRows Candidates

private theorem next_digest_irrelevant (C D E : URow) :
    UpsRelay.compactMsgs C D B_DIGEST false=UpsRelay.compactMsgs C E B_DIGEST false := by
  simp [UpsRelay.compactMsgs,compactInteractions,UpsV3.interactions,Dsl.send,Dsl.recv,
    B_BYTES,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_EDGE,B_BMAP,B_UPB,B_MEMD,
    uMult,uev,Expr.evalWith,uEnv,Dsl.c,Dsl.k,UpsV3.upsId,UpsV3.regs,Dsl.mid,Dsl.smul]

private theorem zero_digests (D : URow) : UpsRelay.compactMsgs (fun _=>0) D B_DIGEST false=[] := by
  simp [UpsRelay.compactMsgs,compactInteractions,UpsV3.interactions,Dsl.send,Dsl.recv,
    B_BYTES,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_EDGE,B_BMAP,B_UPB,B_MEMD,
    uMult,uev,Expr.evalWith,uEnv,Dsl.c,Dsl.k]
  decide

def compactGeneratedDigests (insts : List UpsInst) : List ZkFormal.Near.Msg :=
  (List.range (compactR insts)).flatMap fun r =>
    UpsRelay.compactMsgs (fun x => ((compactCell insts r x : Fp).toNat)) (fun _=>0) B_DIGEST false

def trace (insts : List UpsInst) (L : Nat) : Trace Fp :=
  ⟨fun _=>L,fun _ r c=>(compactCell insts r c : Fp)⟩

/-- Exact physical DIGEST inventory, including every inactive row. -/
theorem digests_at_log (insts : List UpsInst) (L : Nat) (hR : compactR insts≤2^L)
    (t : Nat) (pub : List Fp) (msg : List Fp) :
    tableBusCount compactTable.interactions (trace insts L) t pub B_DIGEST false msg=
      ((compactGeneratedDigests insts).map Msg.toFp).count msg := by
  rw [tableBusCount_eq]
  have he : (List.range ((trace insts L).height t)).flatMap
      (fun r=>rowTraffic compactTable.interactions (trace insts L) t r pub B_DIGEST false)=
      (compactGeneratedDigests insts).map Msg.toFp := by
    simp only [show compactTable.interactions=compactInteractions from rfl,
      Extract.rowTraffic_compact,←List.map_flatMap]
    congr 1
    change (List.range (2^L)).flatMap _=_
    rw [show 2^L=compactR insts+(2^L-compactR insts) by omega,List.range_add,List.flatMap_append]
    have hz : (List.range (2^L-compactR insts)).flatMap (fun r=>
        UpsRelay.compactMsgs (rowC (trace insts L) t (compactR insts+r))
          (rowC (trace insts L) t ((compactR insts+r+1)%(trace insts L).height t)) B_DIGEST false)=[] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro r hr
      have hC : rowC (trace insts L) t (compactR insts+r)=(fun _=>0) := by
        funext x
        simp [rowC,cv,trace,compactCell,show ¬compactR insts+r<compactR insts by omega]
        rfl
      rw [hC,zero_digests]
    simp only [List.flatMap_map] at ⊢
    rw [hz,List.append_nil]
    apply UpsRows.flatMap_congr'
    intro r hr
    rw [next_digest_irrelevant _ _ (fun _=>0)]
    rfl
  rw [he]

theorem digests (insts : List UpsInst) (hR : compactR insts≤2^22)
    (t : Nat) (pub : List Fp) (msg : List Fp) :
    tableBusCount compactTable.interactions (CompactHeight.trace insts) t pub B_DIGEST false msg=
      ((compactGeneratedDigests insts).map Msg.toFp).count msg :=
  digests_at_log insts 22 hR t pub msg


end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
