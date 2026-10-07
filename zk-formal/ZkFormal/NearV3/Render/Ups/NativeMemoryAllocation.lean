import ZkFormal.NearV3.Render.Ups.TreeOutputChain
import ZkFormal.NearV3.Render.Ups.NativeChildMemory
import ZkFormal.NearV3.Render.Ups.MemGrowthParts

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Assign exact new-child memory before constructing positional and serialized fields.
Split branches retain their native inherited-memory arithmetic, which need not equal
an inconsistent old child's memory. -/
def nativeMemoryBase (run : TreeRun) (base : Nat→UpsPartI) (k : Nat) : UpsPartI :=
  {base k with mB :=
    match run.parts[k]? with
    | none => 0
    | some p =>
      if p.kind=.RDB ∨ p.kind=.RDE ∨ p.kind=.PT then
        ((run.parts[k-1]?).map (fun prev => prev.output.memD)).getD 0
      else splitChildMemory run.matched p}

def encodeNativeMemoryParts (recordId : PTrie→Nat) (root : PTrie) (run : TreeRun)
    (base : Nat→UpsPartI) : Option (List UpsPartI) :=
  encodeNativeParts recordId root run (nativeMemoryBase run base)

/-- Upper-node memory is the exact native path-child scalar, before u64 serialization. -/
theorem nativeMemoryBase_upper {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) (base : Nat→UpsPartI) (k : Nat) (p : TreePart)
    (hp : run.parts[k+1]?=some p) (hu : upperKind p.kind) :
    ∃ nextChild, outputPathChild p=some nextChild ∧
      (nativeMemoryBase run base (k+1)).mB=nextChild.memD ∧ nextChild∈run.parts.map TreePart.output := by
  have hn := List.getElem?_eq_some_iff.mp hp |>.1
  have hk : k<run.parts.length := by omega
  let prev := run.parts[k]'hk
  have hprev : run.parts[k]?=some prev := List.getElem?_eq_getElem hk
  refine ⟨prev.output,traceUpsert_outputChild hr hprev hp hu,?_,?_⟩
  · simp [nativeMemoryBase,hp,hprev,show p.kind=.RDB ∨ p.kind=.RDE ∨ p.kind=.PT from hu]
  · exact List.mem_map.mpr ⟨prev,List.mem_of_getElem? hprev,rfl⟩

/-- Exact upper memory assignments fit the wide-carry representation for the native
400-step builder. This does not require output memory to fit u64. -/
theorem nativeMemoryBase_upper_bound {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (hd : fdepth root [0,15]≤400) (hv : v.length<2^24)
    (base : Nat→UpsPartI) (k : Nat) (p : TreePart)
    (hp : run.parts[k+1]?=some p) (hu : upperKind p.kind) :
    (nativeMemoryBase run base (k+1)).mB<2^74 := by
  obtain ⟨nextChild,_,hm,hmem⟩ := nativeMemoryBase_upper hr base k p hp hu
  obtain ⟨prev,hprev,hout⟩ := List.mem_map.mp hmem
  have hb := trace_parts_memory_growth root [0,15] v run hw (by decide) hv hr prev hprev
  rw [hm,←hout]
  omega

/-- Encoding and signing retain the executable new-child memory assignment. -/
theorem nativeInstance_newChildMemory (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeMemoryParts recordId root run base=some Qs) (k : Nat) (hk : k+1<Qs.length)
    (hu : (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=0 ∨
      (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=1 ∨
      (part (nativeInstance recordId baseI root run v Qs) (k+1)).kind=11) :
    ∃ p nextChild, run.parts[k+1]?=some p ∧ outputPathChild p=some nextChild ∧
      (part (nativeInstance recordId baseI root run v Qs) (k+1)).mB=nextChild.memD := by
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr (nativeMemoryBase run base) he (k+1) hk
  have hkind := encodeTreePart_kind henc
  have hupper : upperKind p.kind := by
    rw [hpart] at hu
    change Q.kind=0 ∨ Q.kind=1 ∨ Q.kind=11 at hu
    rw [hkind] at hu
    cases hc : p.kind <;> simp_all [UKind.ix,upperKind]
  obtain ⟨nextChild,hchild,hm,_⟩ := nativeMemoryBase_upper hr base k p hp hupper
  refine ⟨p,nextChild,hp,hchild,?_⟩
  rw [hpart]
  change Q.mB=nextChild.memD
  exact (encodeTreePart_mB henc).trans hm
end ZkFormal.NearV3.Render.UpsGen
