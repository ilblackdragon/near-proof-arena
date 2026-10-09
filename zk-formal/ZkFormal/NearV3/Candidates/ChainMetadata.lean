import ZkFormal.NearV3.Candidates.StoreDuplicateChain
import ZkFormal.NearV3.Candidates.StoreDuplicateComplete
namespace ZkFormal.NearV3.Candidates.ChainMetadata
open ZkFormal.Near ZkFormal.Algebra Render

def metadata (rs : List StoreDuplicateChain.Entry) (eid : Nat) : StoreDuplicateChain.Entry :=
  (rs.find? fun r=>r.eid==eid).getD ⟨eid,false,false,0⟩

theorem metadata_small (rs : List StoreDuplicateChain.Entry) (eid : Nat)
    (h : ∀r∈rs,r.repE<Algebra.P) : (metadata rs eid).repE<Algebra.P := by
  unfold metadata
  cases hf : rs.find? (fun r=>r.eid==eid) with
  | none => change 0<Algebra.P; decide
  | some r => exact h r (List.mem_of_find?_eq_some hf)

def patch (rs : List StoreDuplicateChain.Entry) (n : Nat) (s : NodeS3) : NodeS3 :=
  let m:=metadata rs (eidN n)
  {s with dup:=m.dup,hd:=m.hd,repE:=m.repE}

def assign (rs : List StoreDuplicateChain.Entry) : Nat→List NodeS3→List NodeS3
  | _,[] => []
  | n,s::ss => patch rs n s::assign rs (n+1) ss

theorem assign_length (rs : List StoreDuplicateChain.Entry) (n : Nat) (ss : List NodeS3) :
    (assign rs n ss).length=ss.length := by
  induction ss generalizing n with
  | nil => rfl
  | cons s ss ih => simp [assign,ih]

theorem assign_member (rs : List StoreDuplicateChain.Entry) : ∀(ss : List NodeS3)(n : Nat)(s : NodeS3),
    s∈assign rs n ss → ∃i o,o∈ss ∧ s=patch rs i o
  | [],_,_,h => by simp [assign] at h
  | o::ss,n,s,h => by
    simp only [assign,List.mem_cons] at h
    rcases h with rfl|h
    · exact ⟨n,o,by simp,rfl⟩
    · obtain ⟨i,o,ho,he⟩:=assign_member rs ss (n+1) s h
      exact ⟨i,o,by simp [ho],he⟩

theorem assign_get (rs : List StoreDuplicateChain.Entry) : ∀(ss : List NodeS3)(n i : Nat),
    (assign rs n ss)[i]?=ss[i]?.map (patch rs (n+i))
  | [],_,_ => by simp [assign]
  | s::ss,n,0 => by simp [assign]
  | s::ss,n,i+1 => by
    simpa [assign,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using assign_get rs ss (n+1) i

theorem assign_bytes (rs : List StoreDuplicateChain.Entry) (ss : List NodeS3) (n : Nat) :
    (assign rs n ss).map (fun s=>(s.v.ser false).length)=ss.map (fun s=>(s.v.ser false).length) := by
  induction ss generalizing n with
  | nil => rfl
  | cons s ss ih => simp [assign,patch,ih]

/-- Duplicate/head/representative updates preserve the same complete local
forest view. Semantic duplicate ownership requires actual occurrence coverage. -/
theorem assign_wf (rs : List StoreDuplicateChain.Entry) (ss : List NodeS3) (h : NodeWf3 ss)
    (hid : ∀r∈rs,r.repE<Algebra.P) : NodeWf3 (assign rs 0 ss) := by
  have hg : ∀i (hi : i<(assign rs 0 ss).length),
      ∃(ho : i<ss.length),(assign rs 0 ss)[i]=patch rs i ss[i] := by
    intro i hi
    have ho : i<ss.length := by simpa [assign_length] using hi
    refine ⟨ho,?_⟩
    have hh:=assign_get rs ss 0 i
    simpa [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem ho] using hh
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assign_member rs ss 0 s hs;exact h.wf o ho
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assign_member rs ss 0 s hs;exact h.depth o ho
  · intro i hi;obtain ⟨ho,hget⟩:=hg i hi;rw [hget];exact h.res i ho
  · intro i hi;obtain ⟨ho,hget⟩:=hg i hi;rw [hget];exact h.uses i ho
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assign_member rs ss 0 s hs
    have hh:=h.small o ho
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,metadata_small rs _ hid,hh.2.2.2.2.2⟩
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assign_member rs ss 0 s hs;exact h.canon o ho
  · simpa [assign_length] using h.count
  · simpa [assign_bytes] using h.rows
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assign_member rs ss 0 s hs;exact h.upbLen o ho
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assign_member rs ss 0 s hs;exact h.upbSmall o ho
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assign_member rs ss 0 s hs;exact h.kidCid o ho

theorem metadata_exact (rs : List StoreDuplicateChain.Entry)
    (hn : (rs.map StoreDuplicateChain.Entry.eid).Nodup)
    (r : StoreDuplicateChain.Entry) (hr : r∈rs) : metadata rs r.eid=r := by
  induction rs with
  | nil => simp at hr
  | cons a rs ih =>
    simp only [List.map_cons,List.nodup_cons] at hn
    rcases List.mem_cons.mp hr with rfl|hr
    · simp [metadata]
    · have he : a.eid≠r.eid := by
        intro h
        exact hn.1 (List.mem_map.mpr ⟨r,hr,h.symm⟩)
      simpa [metadata,he] using ih hn.2 hr

private theorem tail_small (ids : List Nat) (prev : Nat) (hp : prev<Algebra.P)
    (hi : ∀i∈ids,i<Algebra.P) :
    ∀r∈StoreDuplicateChain.tailEntries prev ids,r.repE<Algebra.P := by
  induction ids generalizing prev with
  | nil => simp [StoreDuplicateChain.tailEntries]
  | cons i ids ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl|hr
    · exact hp
    · exact ih i (hi i (by simp)) (fun j hj=>hi j (by simp [hj])) r hr

theorem chain_small (ids : List Nat) (hi : ∀i∈ids,i<Algebra.P) :
    ∀r∈StoreDuplicateChain.entries ids,r.repE<Algebra.P := by
  cases ids with
  | nil => simp [StoreDuplicateChain.entries]
  | cons i ids =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl|hr
    · change 0<Algebra.P; decide
    · exact tail_small ids i (hi i (by simp)) (fun j hj=>hi j (by simp [hj])) r hr

theorem assigned_getD (rs : List StoreDuplicateChain.Entry) (vs : List NodeS3)
    (i : Nat) (hi : i<vs.length) :
    (assign rs 0 vs).getD i default=patch rs i (vs.getD i default) := by
  have hh:=assign_get rs vs 0 i
  have ha : i<(assign rs 0 vs).length := by simpa [assign_length] using hi
  simpa [List.getD,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem ha] using hh

theorem assigned_cid (rs : List StoreDuplicateChain.Entry) (vs : List NodeS3)
    (i p : Nat) (hi : i<vs.length) :
    NodeGen3.cidAt (assign rs 0 vs) i p=NodeGen3.cidAt vs i p := by
  simp only [NodeGen3.cidAt,NodeGen3.layN,NodeGen3.rec,assigned_getD rs vs i hi,patch]

theorem node_ok (rs : List StoreDuplicateChain.Entry) (vs : List NodeS3)
    (hn : NodeOk vs) (hid : ∀r∈rs,r.repE<Algebra.P) : NodeOk (assign rs 0 vs) := by
  refine ⟨assign_wf rs vs hn.wf hid,?_,?_,?_,?_,?_⟩
  · simpa [assign_length] using hn.pos
  · intro s hs
    obtain ⟨i,o,ho,rfl⟩:=assign_member rs vs 0 s hs
    exact hn.depth o ho
  · intro s hs
    obtain ⟨i,o,ho,rfl⟩:=assign_member rs vs 0 s hs
    exact hn.lenB o ho
  · simpa [assign_bytes] using hn.rows
  · intro n hni p hp
    have hi : n<vs.length := by simpa [assign_length] using hni
    rw [assigned_getD rs vs n hi] at hp ⊢
    rw [assigned_cid rs vs n p hi]
    exact hn.ucid n hi p hp

def patchValue (rs : List StoreDuplicateChain.Entry) (e : ValE) : ValE :=
  let m:=metadata rs (eidV e)
  {e with dup:=m.dup,hd:=m.hd,repE:=m.repE}

def assignValues (rs : List StoreDuplicateChain.Entry) (es : List ValE) : List ValE :=
  es.map (patchValue rs)

theorem value_wf (rs : List StoreDuplicateChain.Entry) (es : List ValE)
    (h : ValWf es) (hid : ∀r∈rs,r.repE<Algebra.P) : ValWf (assignValues rs es) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro e he
    obtain ⟨o,ho,rfl⟩ := List.mem_map.mp he
    exact h.shape o ho
  · intro e he
    obtain ⟨o,ho,rfl⟩ := List.mem_map.mp he
    have hh:=h.canon o ho
    exact ⟨hh.1,hh.2.1,metadata_small rs _ hid,hh.2.2.2⟩
  · intro t ht
    have ho : t+1<es.length := by simpa [assignValues] using ht
    simpa [assignValues,patchValue] using h.ids t ho
  · intro ht
    have ho : 0<es.length := by simpa [assignValues] using ht
    simpa [assignValues,patchValue] using h.first ho
  · have heq : ((assignValues rs es).map fun e=>if e.vz then 1 else e.len)=
        (es.map fun e=>if e.vz then 1 else e.len) := by
      simp only [assignValues,List.map_map,Function.comp_def,patchValue]
      rfl
    rw [heq]
    exact h.rows

theorem chain_metadata (ids : List Nat) (hn : ids.Nodup)
    (r : StoreDuplicateChain.Entry) (hr : r∈StoreDuplicateChain.entries ids) :
    metadata (StoreDuplicateChain.entries ids) r.eid=r := by
  apply metadata_exact _ _ r hr
  simpa [StoreDuplicateChain.entity_ids] using hn

theorem node_flags (rs : List StoreDuplicateChain.Entry)
    (hn : (rs.map StoreDuplicateChain.Entry.eid).Nodup)
    (r : StoreDuplicateChain.Entry) (hr : r∈rs) (i : Nat) (he : r.eid=eidN i)
    (s : NodeS3) :
    (patch rs i s).dup=r.dup ∧ (patch rs i s).hd=r.hd ∧ (patch rs i s).repE=r.repE := by
  simp [patch,←he,metadata_exact rs hn r hr]

theorem value_flags (rs : List StoreDuplicateChain.Entry)
    (hn : (rs.map StoreDuplicateChain.Entry.eid).Nodup)
    (r : StoreDuplicateChain.Entry) (hr : r∈rs) (e : ValE) (he : r.eid=eidV e) :
    (patchValue rs e).dup=r.dup ∧ (patchValue rs e).hd=r.hd ∧ (patchValue rs e).repE=r.repE := by
  simp [patchValue,←he,metadata_exact rs hn r hr]

/-- Concrete chain metadata supports the real count-extended local renderers.
Global class coverage/order and equality of their byte payloads remain separate. -/
theorem complete (rs : List StoreDuplicateChain.Entry) (vs : List NodeS3) (es : List ValE)
    (hn : NodeOk vs) (hv : ValWf es) (hid : ∀r∈rs,r.repE<Algebra.P)
    (t : Nat) (pub : List Fp) :
    TableLocal Rcpt.Candidates.SizeCount.nodeTable
      (TrieCountHeight.node (assign rs 0 vs) pub) t pub ∧
    TableLocal Rcpt.Candidates.SizeCount.valTable
      (TrieCountHeight.value (assignValues rs es) pub) t pub :=
  ⟨(TrieCountComplete.node_complete _ (node_ok rs vs hn hid) t pub).1,
   (TrieCountComplete.value_complete _ ⟨value_wf rs es hv hid⟩ t pub).1⟩

end ZkFormal.NearV3.Candidates.ChainMetadata
