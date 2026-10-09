import ZkFormal.NearV3.Candidates.ProcPriorOverlayDataTransport
namespace ZkFormal.NearV3.Candidates.ProcPriorOverlayComponentRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcPriorVertical4Linear ProcPriorVertical4Clock ProcPriorVertical4ClockCases
open ProcPriorVertical4DataEval ProcPriorOverlayCuts ProcPriorOverlayGeometry

theorem current (bs : List NativeBlock) (hc:0<cutMemory bs ∧ cutMemory bs<cutIds bs ∧
      cutIds bs<cutRaw bs ∧ cutRaw bs<2^22)
    (source : Nat→Trace Fp) (i : Nat) (T : Air.Table) (hT:T∈components)
    (hlog:(source i).log 0=22) (hlocal:TableLocal T (source i) 0 [])
    (used : Nat) (hused:used<stop bs i-start bs i)
    (hz:∀j,used≤j→(source i).cell 0 j=fun _=>0)
    (r tt : Nat) (hr:r<2^22) (hi:stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r=i)
    (pub : List Fp) (e : Expr) (he:e∈T.constraints) :
    (expression e).eval (trace bs (fun n=>(source n).cell 0)) tt r pub=0 := by
  have hcol:=component_columns T hT e (List.mem_append_left _ he)
  have hpub:=ProcPriorOverlayDataTransport.component_pub T hT e (List.mem_append_left _ he)
  rw [ProcPriorOverlayDataTransport.translated bs _ tt r pub e hcol hpub]
  have hg:=position bs hc (fun n=>(source n).cell 0) r hr
  dsimp only at hg
  rw [hi] at hg
  obtain ⟨hstart,hstop,hmax,hd,hf,hl,hn⟩:=hg
  rw [hd,hf,hl]
  by_cases hend:r+1=stop bs i
  · have hlast:r-start bs i+1=stop bs i-start bs i:=by omega
    have hu:used≤r-start bs i:=by omega
    unfold logicalEnv
    rw [hz _ hu]
    apply ProcPriorOverlayPadding.constraints T hT
    · left
      simp only [hlast,decide_true,flag,ite_true]
      decide +kernel
    · exact he
  · have hnext:r+1<stop bs i:=by omega
    rw [hn hnext]
    have hh:=ProcPriorOverlayWindowLocal.constraints T hT (source i) 0 hlog hlocal used
      (stop bs i-start bs i) hused (by omega) hz (r-start bs i) (by omega) e he
    have he:logicalEnv ((source i).cell 0 (r-start bs i)) ((source i).cell 0 (r-start bs i+1))
        (decide (r-start bs i=0)) (decide (r-start bs i+1=stop bs i-start bs i))=
      ProcPriorOverlayWindowLocal.localEnv ((source i).cell 0) (stop bs i-start bs i) (r-start bs i) := by
      have hlast:¬r-start bs i+1=stop bs i-start bs i:=by omega
      simp only [logicalEnv,ProcPriorOverlayWindowLocal.localEnv,flag,decide_eq_true_eq,hlast,ite_false]
      congr 1
    rwa [he]
theorem bit (bs : List NativeBlock) (hc:0<cutMemory bs ∧ cutMemory bs<cutIds bs ∧
      cutIds bs<cutRaw bs ∧ cutRaw bs<2^22)
    (source : Nat→Trace Fp) (i : Nat) (T : Air.Table) (hT:T∈components)
    (hlog:(source i).log 0=22) (hlocal:TableLocal T (source i) 0 [])
    (used : Nat) (hused:used<stop bs i-start bs i)
    (hz:∀j,used≤j→(source i).cell 0 j=fun _=>0)
    (r tt : Nat) (hr:r<2^22) (hi:stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r=i)
    (pub : List Fp) (a : Interaction) (ha:a∈T.interactions) (e : Expr) (he:e∈a.mult) :
    (expression e).eval (trace bs (fun n=>(source n).cell 0)) tt r pub=0 ∨
    (expression e).eval (trace bs (fun n=>(source n).cell 0)) tt r pub=1 := by
  have hcol:=component_columns T hT e (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a,ha,List.mem_append_left _ he⟩))
  have hpub:=ProcPriorOverlayDataTransport.component_pub T hT e (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a,ha,List.mem_append_left _ he⟩))
  simp only [ProcPriorOverlayDataTransport.translated bs _ tt r pub e hcol hpub]
  have hg:=position bs hc (fun n=>(source n).cell 0) r hr
  dsimp only at hg
  rw [hi] at hg
  obtain ⟨hstart,hstop,hmax,hd,hf,hl,hn⟩:=hg
  rw [hd,hf,hl]
  by_cases hend:r+1=stop bs i
  · have hlast:r-start bs i+1=stop bs i-start bs i:=by omega
    have hu:used≤r-start bs i:=by omega
    unfold logicalEnv
    rw [hz _ hu]
    exact Or.inl (ProcPriorOverlayPadding.multiplicity T hT _ _ _ _ a ha e he)
  · have hnext:r+1<stop bs i:=by omega
    rw [hn hnext]
    have hh:=ProcPriorOverlayWindowLocal.bits T hT (source i) 0 hlog hlocal used
      (stop bs i-start bs i) hused (by omega) hz (r-start bs i) (by omega) a ha e he
    have he:logicalEnv ((source i).cell 0 (r-start bs i)) ((source i).cell 0 (r-start bs i+1))
        (decide (r-start bs i=0)) (decide (r-start bs i+1=stop bs i-start bs i))=
      ProcPriorOverlayWindowLocal.localEnv ((source i).cell 0) (stop bs i-start bs i) (r-start bs i) := by
      have hlast:¬r-start bs i+1=stop bs i-start bs i:=by omega
      simp only [logicalEnv,ProcPriorOverlayWindowLocal.localEnv,flag,decide_eq_true_eq,hlast,ite_false]
      congr 1
    rwa [he]
end ZkFormal.NearV3.Candidates.ProcPriorOverlayComponentRows
