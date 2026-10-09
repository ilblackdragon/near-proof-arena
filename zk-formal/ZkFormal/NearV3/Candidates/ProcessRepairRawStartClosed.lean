import ZkFormal.NearV3.Candidates.ProcessRepairRawBytes
import ZkFormal.NearV3.Candidates.ProcPriorRawOrigin
import ZkFormal.NearV3.Qv.Extract.SupplierStreams
namespace ZkFormal.NearV3.Candidates.ProcessRepairRawStartClosed
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ProcPriorRoutedRawSource (raw)
open ProcPriorRoutedRawBytes ProcPriorRawFrame
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem live {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) {r:Nat} (hr:r<tr.height 0)
    (hm:bytes.multNat tr 0 r pub≠0) :
    cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv (raw tr) 0 r act=1 ∧ cv (raw tr) 0 r present=1 := by
  have hL:=ProcessRepairRawBytes.overlay_local view
  rw [bytes_mult] at hm
  change (if (raw tr).cell 0 r (ProcPriorVertical4Linear.stage 2)*(raw tr).cell 0 r byteGate=1 then 1 else 0)+0≠0 at hm
  have hp:(raw tr).cell 0 r (ProcPriorVertical4Linear.stage 2)*(raw tr).cell 0 r byteGate=1:=by
    split at hm
    · assumption
    · simp at hm
  have hzero (x:Nat) (hx:cv (raw tr) 0 r x=0):(raw tr).cell 0 r x=0:=by
    change (raw tr).cell 0 r x=Fp.ofNat 0
    exact (Fp.ofNat_toNat _).symm.trans (congrArg Fp.ofNat hx)
  have hsb:=hL.bool hr (ProcPriorVerticalMemorySound.window_member
    (Table.boolC (ProcPriorVertical4Linear.stage 2)) (by simp [ProcPriorVertical4Linear.windows]))
  have hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1:=by
    by_cases hz:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=0
    · rw [hzero _ hz] at hp;grind only
    · omega
  have hgb:=ProcPriorRawSound.flag hL hr hs byteGate (by simp)
  have hg:cv (raw tr) 0 r byteGate=1:=by
    by_cases hz:cv (raw tr) 0 r byteGate=0
    · rw [hzero _ hz] at hp;grind only
    · omega
  obtain ⟨q,hq⟩:=ProcPriorRawSound.zdvd hL hr hs
    (sub (c byteGate) (.mul (c act) (c present))) (by simp [constraints])
  change zev (tenv (raw tr) 0 r pub) (sub (c byteGate) (.mul (c act) (c present)))=2013265921*q at hq
  zs hq [hg]
  have ha:=ProcPriorRawSound.flag hL hr hs act (by simp)
  have hpres:=ProcPriorRawSound.flag hL hr hs present (by simp)
  have hh:cv (raw tr) 0 r act=0 ∨ cv (raw tr) 0 r act=1:=by omega
  rcases hh with hh|hh <;> simp only [hh] at hq <;> simp only [Int.natCast_zero,Int.natCast_one,Int.zero_mul,Int.one_mul] at hq
  · omega
  · exact ⟨hs,hh,by omega⟩

theorem start_closed {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) :
    Qv.Extract.StartClosed ((List.range (tr.height 0)).flatMap
      (fun r=>ZkFormal.Near.rowTraffic [bytes] tr 0 r pub B_VBYTES true)) := by
  intro m hm
  obtain ⟨r,hr,hm⟩:=List.mem_flatMap.mp hm
  have hr':r<tr.height 0:=List.mem_range.mp hr
  have hrow (q:Nat):ZkFormal.Near.rowTraffic [bytes] tr 0 q pub B_VBYTES true=
      List.replicate (bytes.multNat tr 0 q pub) (bytes.msgVal tr 0 q pub):=by
    simp only [ZkFormal.Near.rowTraffic,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rfl
  rw [hrow] at hm
  obtain ⟨hmult,rfl⟩:=List.mem_replicate.mp hm
  have hl:=ProcessRepairRawBytes.overlay_local view
  obtain ⟨hs,ha,hp⟩:=live view hr' hmult
  have hheight:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide)
    (view.component 19 (by decide +kernel) (by decide)).log_le
  obtain ⟨f,hfr,hf,hfs,hfirst,hfa,hpos,_,hfields⟩:=ProcPriorRawOrigin.origin hl
    (show (raw tr).height 0≤2013265921 by change tr.height 0≤_;omega) hr' hs ha
  have hfp:cv (raw tr) 0 f present=1:=by rw [←hfields present (by simp)];exact hp
  have hg:=ProcPriorRawSound.byte_gate hl hf hfs hfa hfp
  have hm:bytes.multNat tr 0 f pub≠0:=by
    rw [bytes_mult]
    have hc (x:Nat) (hx:cv (raw tr) 0 f x=1):(raw tr).cell 0 f x=Fp.ofNat 1:=
      (Fp.ofNat_toNat _).symm.trans (congrArg Fp.ofNat hx)
    change (if (raw tr).cell 0 f (ProcPriorVertical4Linear.stage 2)*(raw tr).cell 0 f byteGate=1 then 1 else 0)+0≠0
    rw [hc _ hfs,hc _ hg]
    decide +kernel
  refine ⟨bytes.msgVal tr 0 f pub,?_,?_⟩
  · apply List.mem_flatMap.mpr
    refine ⟨f,List.mem_range.mpr hf,?_⟩
    rw [hrow]
    exact List.mem_replicate.mpr ⟨hm,rfl⟩
  · rw [bytes_message,bytes_message]
    change ((raw tr).cell 0 f vid,(raw tr).cell 0 f pos)=((raw tr).cell 0 r vid,0)
    apply Prod.ext
    · have hv:=hfields vid (by simp)
      exact (Fp.ofNat_toNat _).symm.trans ((congrArg Fp.ofNat hv.symm).trans (Fp.ofNat_toNat _))
    · exact (Fp.ofNat_toNat _).symm.trans (congrArg Fp.ofNat hpos)
end ZkFormal.NearV3.Candidates.ProcessRepairRawStartClosed
