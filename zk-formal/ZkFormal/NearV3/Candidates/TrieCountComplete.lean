import ZkFormal.NearV3.Candidates.SizeRecordTraffic
namespace ZkFormal.NearV3.Candidates.TrieCountComplete
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render ZkFormal.NearV3.Render
open Rcpt.Candidates.SizeCount SizeRecordTraffic

def nodeSize (es : List NodeS3) : Near.Msg :=
  [0,((es.filter fun e=>!e.dup).map fun e=>(e.v.ser false).length).sum,
   (es.filter fun e=>!e.dup).length]
def valueSize (es : List ValE) : Near.Msg :=
  [1,((es.filter fun e=>!e.vz && !e.dup).map ValE.len).sum,
   (es.filter fun e=>!e.dup).length]

/-- The semantic count-extended table traffic: all original buses, with the
SIZE message explicitly carrying payload bytes and record-header count. -/
def withSize (tf : Traffic) (msg : Near.Msg) : Traffic :=
  ⟨fun b=>if b=B_SIZE then [msg] else tf.sends b,
   fun b=>if b=B_SIZE then [] else tf.recvs b⟩

theorem node_traffic (es : List NodeS3) (ok : NodeOk es) (t : Nat) (pub : List Fp) :
    TableTraffic nodeTable.interactions (TrieCountHeight.node es pub) t pub
      (withSize (nodeTraffic3 es) (nodeSize es)) := by
  intro b m
  by_cases hb : b=B_SIZE
  · subst b
    rw [SizeRecordTraffic.node_traffic es ok,SizeRecordTraffic.node_traffic es ok]
    simp [withSize,nodeSize,nodeMessage,Near.Msg.toFp,List.count_cons]
  · rw [TrieCountTraffic.node_non_size es pub t b true m hb,
      TrieCountTraffic.node_non_size es pub t b false m hb]
    simpa only [withSize,if_neg hb] using (TrieHeight.node_complete es ok t pub).2.1 b m

theorem value_traffic (es : List ValE) (ok : ValOk es) (t : Nat) (pub : List Fp) :
    TableTraffic valTable.interactions (TrieCountHeight.value es pub) t pub
      (withSize (valTraffic es) (valueSize es)) := by
  intro b m
  by_cases hb : b=B_SIZE
  · subst b
    rw [SizeRecordTraffic.value_traffic es ok,SizeRecordTraffic.value_traffic es ok]
    simp [withSize,valueSize,valueMessage,Near.Msg.toFp,List.count_cons]
  · rw [TrieCountTraffic.value_non_size es pub t b true m hb,
      TrieCountTraffic.value_non_size es pub t b false m hb]
    simpa only [withSize,if_neg hb] using (TrieHeight.value_complete es ok t pub).2.1 b m

theorem node_complete (es : List NodeS3) (ok : NodeOk es) (t : Nat) (pub : List Fp) :
    TableLocal nodeTable (TrieCountHeight.node es pub) t pub ∧
    TableTraffic nodeTable.interactions (TrieCountHeight.node es pub) t pub
      (withSize (nodeTraffic3 es) (nodeSize es)) ∧
    (TrieCountHeight.node es pub).log t=22 :=
  ⟨TrieCountHeight.node_local es ok t pub,node_traffic es ok t pub,rfl⟩

theorem value_complete (es : List ValE) (ok : ValOk es) (t : Nat) (pub : List Fp) :
    TableLocal valTable (TrieCountHeight.value es pub) t pub ∧
    TableTraffic valTable.interactions (TrieCountHeight.value es pub) t pub
      (withSize (valTraffic es) (valueSize es)) ∧
    (TrieCountHeight.value es pub).log t=22 :=
  ⟨TrieCountHeight.value_local es ok t pub,value_traffic es ok t pub,rfl⟩
end ZkFormal.NearV3.Candidates.TrieCountComplete
