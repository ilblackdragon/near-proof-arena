import ZkFormal.NearV3.Candidates.StoreDuplicateMetadata
import ZkFormal.NearV3.Render.ValGen
namespace ZkFormal.NearV3.Candidates.ValueDuplicateMetadata
open ZkFormal.Near ZkFormal.Algebra NearSpec ZkFormal.NearV3.Render
open StoreDuplicateMetadata

def patch (rs : List Occurrence) (tau : Nat) (e : ValE) : ValE :=
  let rep:=representativeId rs (tau,toBytes e.bytes)
  {e with dup:=!(eidV e==rep),hd:=(eidV e==rep),repE:=rep}

def assign (rs : List Occurrence) (tau : ValE→Nat) (es : List ValE) : List ValE :=
  es.map fun e=>patch rs (tau e) e

theorem assign_wf (rs : List Occurrence) (tau : ValE→Nat) (es : List ValE)
    (h : ValWf es) (hid : ∀r∈rs,r.eid<P) : ValWf (assign rs tau es) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro e he
    obtain ⟨o,ho,rfl⟩ := List.mem_map.mp he
    exact h.shape o ho
  · intro e he
    obtain ⟨o,ho,rfl⟩ := List.mem_map.mp he
    have hh:=h.canon o ho
    exact ⟨hh.1,hh.2.1,representative_small rs _ hid,hh.2.2.2⟩
  · intro t ht
    have ho : t+1<es.length := by simpa [assign] using ht
    simpa [assign,patch] using h.ids t ho
  · intro ht
    have ho : 0<es.length := by simpa [assign] using ht
    simpa [assign,patch] using h.first ho
  · simpa [assign,patch,List.map_map,Function.comp_def] using h.rows

theorem assign_bytes (rs : List Occurrence) (tau : ValE→Nat) (es : List ValE) :
    (assign rs tau es).map ValE.bytes=es.map ValE.bytes := by
  simp [assign,patch,List.map_map,Function.comp_def]
end ZkFormal.NearV3.Candidates.ValueDuplicateMetadata
