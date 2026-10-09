import ZkFormal.NearV3.Candidates.CompactHeight
import ZkFormal.NearV3.Render.Ups.CompactExtract.TableTraffic
import ZkFormal.NearV3.Render.Ups.RelayNativeInventory

namespace ZkFormal.NearV3.Candidates.CompactPhysicalShaBytes
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render Render.UpsGen Render.UpsRelay UpsRows

private theorem next_irrelevant (C D E : URow) :
    UpsRelay.compactMsgs C D B_BYTES true=UpsRelay.compactMsgs C E B_BYTES true := by
  simp [UpsRelay.compactMsgs,compactInteractions,UpsV3.interactions,Dsl.send,Dsl.recv,
    B_BYTES,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_EDGE,B_BMAP,B_UPB,B_MEMD,
    uMult,uev,Expr.evalWith,uEnv,Dsl.c,Dsl.k,UpsV3.upsId,Dsl.mid,Dsl.smul]

private theorem zero_bytes (D : URow) : UpsRelay.compactMsgs (fun _=>0) D B_BYTES true=[] := by
  simp [UpsRelay.compactMsgs,compactInteractions,UpsV3.interactions,Dsl.send,Dsl.recv,
    B_BYTES,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_EDGE,B_BMAP,B_UPB,B_MEMD,
    uMult,uev,Expr.evalWith,uEnv,Dsl.c,Dsl.k]
  decide

def trace (insts : List UpsInst) (L : Nat) : Trace Fp :=
  ⟨fun _=>L,fun _ r c=>(compactCell insts r c : Fp)⟩

/-- Exact physical byte inventory, including all inactive rows. -/
theorem bytes_at_log (insts : List UpsInst) (L : Nat) (hR : compactR insts≤2^L)
    (t : Nat) (pub : List Fp) (msg : List Fp) :
    tableBusCount compactTable.interactions (trace insts L) t pub B_BYTES true msg=
      ((compactGeneratedBytes insts).map Msg.toFp).count msg := by
  rw [tableBusCount_eq]
  have he : (List.range ((trace insts L).height t)).flatMap
      (fun r=>rowTraffic compactTable.interactions (trace insts L) t r pub B_BYTES true)=
      (compactGeneratedBytes insts).map Msg.toFp := by
    simp only [show compactTable.interactions=compactInteractions from rfl,
      Extract.rowTraffic_compact,←List.map_flatMap]
    congr 1
    change (List.range (2^L)).flatMap _=_
    rw [show 2^L=compactR insts+(2^L-compactR insts) by omega,List.range_add,List.flatMap_append]
    have hz : (List.range (2^L-compactR insts)).flatMap (fun r=>
        UpsRelay.compactMsgs (rowC (trace insts L) t (compactR insts+r))
          (rowC (trace insts L) t ((compactR insts+r+1)%(trace insts L).height t)) B_BYTES true)=[] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro r hr
      have hC : rowC (trace insts L) t (compactR insts+r)=(fun _=>0) := by
        funext x
        simp [rowC,cv,trace,compactCell,show ¬compactR insts+r<compactR insts by omega]
        rfl
      rw [hC,zero_bytes]
    simp only [List.flatMap_map] at ⊢
    rw [hz,List.append_nil]
    apply UpsRows.flatMap_congr'
    intro r hr
    rw [next_irrelevant _ _ (fun _=>0)]
    rfl
  rw [he]

theorem bytes (insts : List UpsInst) (hR : compactR insts≤2^22)
    (t : Nat) (pub : List Fp) (msg : List Fp) :
    tableBusCount compactTable.interactions (CompactHeight.trace insts) t pub B_BYTES true msg=
      ((compactGeneratedBytes insts).map Msg.toFp).count msg :=
  bytes_at_log insts 22 hR t pub msg

/-- Modular renderer messages and SHA's natural-byte messages have identical
field encodings, even before imposing any separate no-wrap bound. -/
theorem sha_bytes_field (jobs : List Sha.Gen.Msg) :
    ((jobs.flatMap shaByteMsgs).map Msg.toFp)=(Sha.Gen.expectedBytes jobs).map Msg.toFp := by
  have hm : ∀n,Fp.ofNat (n%Algebra.P)=Fp.ofNat n := by
    intro n
    apply Fp.ext
    simp only [Fp.toNat_ofNat,Nat.mod_mod]
  simp only [shaByteMsgs,Sha.Gen.expectedBytes,List.map_flatMap,List.map_map,
    Function.comp_def,Msg.toFp,List.map_cons,List.map_nil,hm]

/-- Actual log22 compact output bytes feed exactly the native output-node SHA
jobs of the SAME allocated scheduler witness list. Fresh values and sanity
messages are separate codec/scheduler producers. -/
theorem native_bytes {us : List Assembly.SchedulerUpsertWitness} {insts : List UpsInst}
    (hl : insts.length=us.length)
    (ha : ∀tau u I,us[tau]?=some u→insts[tau]?=some I→
      AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I)
    (hR : compactR insts≤2^22) (t : Nat) (pub : List Fp) (msg : List Fp) :
    tableBusCount compactTable.interactions (CompactHeight.trace insts) t pub B_BYTES true msg=
      ((Sha.Gen.expectedBytes (compactNodeJobs us)).map Msg.toFp).count msg := by
  rw [bytes insts hR t pub msg,compactGeneratedBytes_nodeJobs hl ha,sha_bytes_field]

/-- The caller's chosen native instances supply both local legality and exact
SHA output-byte traffic; compact capacity is derived from their native charges. -/
theorem allocated {us : List Assembly.SchedulerUpsertWitness} {insts : List UpsInst}
    (hl : insts.length=us.length) (hpos : 1≤us.length) (hlen : us.length≤32)
    (ha : ∀tau u I,us[tau]?=some u→insts[tau]?=some I→
      AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I)
    (hout : (us.map (fun u=>Assembly.outputByteCharge u.run)).sum≤2131072)
    (t : Nat) (pub : List Fp) :
    TableLocal compactTable (CompactHeight.trace insts) t pub ∧
    ∀msg,tableBusCount compactTable.interactions (CompactHeight.trace insts) t pub B_BYTES true msg=
      ((Sha.Gen.expectedBytes (compactNodeJobs us)).map Msg.toFp).count msg := by
  have hi:=fun tau u I hu hI=>(ha tau u I hu hI).1
  have hcap : compactR insts+1≤2^22 := by
    rw [compact_rows_exact hl hi]
    exact compact_rows_fit hlen hout
  exact ⟨CompactHeight.trace_local insts (compact_allocated_constraints hl hpos hi hcap hcap) t pub,
    fun msg=>native_bytes hl ha (by omega) t pub msg⟩

end ZkFormal.NearV3.Candidates.CompactPhysicalShaBytes
