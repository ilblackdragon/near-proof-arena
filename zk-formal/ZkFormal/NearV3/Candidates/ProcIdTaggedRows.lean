import ZkFormal.NearV3.Candidates.ProcIdTaggedLocal
namespace ZkFormal.NearV3.Candidates.ProcIdTaggedRows
open ZkFormal.NearV3.Assembly.CodecDigest ProcIdTaggedCells ProcIdTaggedLocal

def block (ids : List Nat) (b : NativeBlock) : List Tagged :=
  (ProcPriorIdRows.rows ids b.old.links).map (fun r=>(b.run.tau,r))
def rows (ids : NativeBlock→List Nat) (bs : List NativeBlock) : List Tagged :=
  bs.flatMap (fun b=>block (ids b) b)
def Chain {α : Type} (R : α→α→Prop) (xs : List α) :=
  ∀i a b,xs[i]?=some a→xs[i+1]?=some b→R a b

theorem chain_append {α : Type} (R : α→α→Prop) (xs ys : List α)
    (hx:Chain R xs) (hy:Chain R ys)
    (hab:∀a∈xs,∀b,ys[0]?=some b→R a b) : Chain R (xs++ys) := by
  intro i a b ha hb
  by_cases hi:i<xs.length
  · rw [List.getElem?_append_left hi] at ha
    by_cases hj:i+1<xs.length
    · rw [List.getElem?_append_left hj] at hb
      exact hx i a b ha hb
    · rw [List.getElem?_append_right (by omega)] at hb
      have he:i+1-xs.length=0:=by omega
      rw [he] at hb
      exact hab a (List.mem_of_getElem? ha) b hb
  · rw [List.getElem?_append_right (by omega)] at ha hb
    have he:i+1-xs.length=(i-xs.length)+1:=by omega
    rw [he] at hb
    exact hy (i-xs.length) a b ha hb

theorem block_chain (ids : List Nat) (b : NativeBlock) : Chain Adjacent (block ids b) := by
  intro i a c ha hc
  simp only [block,List.getElem?_map,Option.map_eq_some_iff] at ha hc
  obtain ⟨a',ha,rfl⟩:=ha
  obtain ⟨c',hc,rfl⟩:=hc
  obtain ⟨pre,post,he⟩:=ProcPriorIndexed.pair_split (ProcPriorIdRows.rows ids b.old.links) i a' c' ha hc
  exact Or.inl ⟨rfl,ProcPriorIdNext.rows_next ids b.old.links pre post a' c' he,
    ProcPriorIdNext.pair_order ids b.old.links pre post a' c' he⟩

theorem block_first (ids : List Nat) (b : NativeBlock) (a : Tagged)
    (h:(block ids b)[0]?=some a) : a.2.before=none := by
  simp only [block,List.getElem?_map,Option.map_eq_some_iff] at h
  obtain ⟨a',ha,rfl⟩:=h
  exact ProcPriorIdNext.first_zero ids b.old.links a' ha

theorem first (ids : NativeBlock→List Nat) (bs : List NativeBlock) (a : Tagged)
    (h:(rows ids bs)[0]?=some a) : a.2.before=none := by
  induction bs with
  | nil=>simp [rows] at h
  | cons b bs ih=>
    change (block (ids b) b++rows ids bs)[0]?=some a at h
    by_cases hh:(block (ids b) b).length=0
    · have he:block (ids b) b=[]:=List.length_eq_zero_iff.mp hh
      rw [he,List.nil_append] at h
      exact ih h
    · rw [List.getElem?_append_left (by omega)] at h
      exact block_first (ids b) b a h

theorem mem_origin (ids : NativeBlock→List Nat) (bs : List NativeBlock) (a : Tagged)
    (ha:a∈rows ids bs) : ∃b∈bs,∃r∈ProcPriorIdRows.rows (ids b) b.old.links,a=(b.run.tau,r) := by
  obtain ⟨b,hb,ha⟩:=List.mem_flatMap.mp ha
  obtain ⟨r,hr,he⟩:=List.mem_map.mp ha
  exact ⟨b,hb,r,hr,he.symm⟩

theorem chain (ids : NativeBlock→List Nat) (bs : List NativeBlock) (start : Nat)
    (ho:∀i b,bs[i]?=some b→b.run.tau=start+i) : Chain Adjacent (rows ids bs) := by
  induction bs generalizing start with
  | nil=>intro i a b ha; simp [rows] at ha
  | cons b bs ih=>
    have hbt:b.run.tau=start:=by simpa using ho 0 b (by simp)
    have hot:∀i c,bs[i]?=some c→c.run.tau=(start+1)+i := by
      intro i c hc
      have h:=ho (i+1) c (by simpa using hc)
      omega
    change Chain Adjacent (block (ids b) b++rows ids bs)
    apply chain_append Adjacent _ _ (block_chain (ids b) b) (ih (start+1) hot)
    intro a ha c hc
    obtain ⟨ar,har,he⟩:=List.mem_map.mp ha
    have hat:a.1=b.run.tau:=by rw [←he]
    obtain ⟨d,hd,dr,hdr,hec⟩:=mem_origin ids bs c (List.mem_of_getElem? hc)
    obtain ⟨j,hj⟩:=List.mem_iff_getElem?.mp hd
    have hdt:=hot j d hj
    exact Or.inr ⟨by rw [hat,hec]; dsimp only; omega,first ids bs c hc⟩
end ZkFormal.NearV3.Candidates.ProcIdTaggedRows
