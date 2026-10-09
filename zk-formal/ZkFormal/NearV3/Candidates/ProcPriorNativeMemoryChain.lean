import ZkFormal.NearV3.Candidates.ProcPriorNativeMemoryPair
namespace ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
open ProcPriorRows ProcPriorEvents
open ZkFormal.NearV3.Assembly.CodecDigest

def Follows (a b : Tagged) : Prop :=
  b.row.before=(if address a=address b then ProcPriorValues.value a.row.event else ProcPriorCarry.zero) ∧
  (a.row.event.query=true → address a≠address b)
def Chain : List Tagged→Prop
  | []=>True
  | [_]=>True
  | a::b::xs=>Follows a b ∧ Chain (b::xs)

theorem chain_of_pairs (xs : List Tagged)
    (h:∀j a b,xs[j]?=some a→xs[j+1]?=some b→Follows a b) : Chain xs := by
  induction xs with
  | nil=>trivial
  | cons a xs ih=>
    cases xs with
    | nil=>trivial
    | cons b ys=>
      refine ⟨h 0 a b rfl rfl,ih ?_⟩
      intro j u v hu hv
      exact h (j+1) u v hu hv

theorem tagged_chain (b : NativeBlock) : Chain (tagged b) := by
  apply chain_of_pairs
  intro j a c ha hc
  unfold tagged at ha hc
  rw [List.getElem?_map] at ha hc
  obtain ⟨ar,har,hea⟩:=Option.map_eq_some_iff.mp ha
  obtain ⟨cr,hcr,hec⟩:=Option.map_eq_some_iff.mp hc
  subst a;subst c
  obtain ⟨pre,post,hs⟩:=ProcPriorIndexed.pair_split (rows b.pub.ids b.old.links) j ar cr har hcr
  have hh:=ProcPriorIndexed.pair_native b.pub.ids b.old.links pre post ar cr hs
  have he:(address ⟨b.run.tau,ar⟩=address ⟨b.run.tau,cr⟩) ↔ ar.event.link=cr.event.link := by
    simp only [address];omega
  exact ⟨by simpa only [he] using hh.1,fun hq heq=>hh.2 hq (he.mp heq)⟩

theorem tagged_first (b : NativeBlock) (a : Tagged) (h:(tagged b)[0]?=some a) :
    a.row.before=ProcPriorCarry.zero := by
  unfold tagged at h
  rw [List.getElem?_map] at h
  obtain ⟨r,hr,he⟩:=Option.map_eq_some_iff.mp h
  subst a
  exact ProcPriorIndexed.first_zero _ _ _ hr

theorem chain_append (xs ys : List Tagged) (hx:Chain xs) (hy:Chain ys)
    (hb:∀a∈xs,∀b,ys[0]?=some b→Follows a b) : Chain (xs++ys) := by
  induction xs with
  | nil=>exact hy
  | cons a xs ih=>
    cases xs with
    | nil=>
      cases ys with
      | nil=>trivial
      | cons b ys=>exact ⟨hb a (by simp) b rfl,hy⟩
    | cons c xs=>
      exact ⟨hx.1,ih hx.2 (fun a ha=>hb a (by simp [ha]))⟩

theorem tagged_member (b : NativeBlock) (a : Tagged) (ha:a∈tagged b) :
    a.tau=b.run.tau ∧ a.row∈rows b.pub.ids b.old.links := by
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp ha
  exact ⟨rfl,hr⟩

theorem all_first (bs : List NativeBlock) (a : Tagged) (ha:(allRows bs)[0]?=some a) :
    a.row.before=ProcPriorCarry.zero := by
  induction bs with
  | nil=>simp [allRows] at ha
  | cons b bs ih=>
    change (tagged b++allRows bs)[0]?=some a at ha
    cases ht:tagged b with
    | nil=>rw [ht,List.nil_append] at ha;exact ih ha
    | cons c cs=>
      have hh:(tagged b)[0]?=some a := by simpa only [ht,List.cons_append,List.getElem?_cons_zero] using ha
      exact tagged_first b a hh

theorem all_chain (bs : List NativeBlock)
    (hn:∀b∈bs,b.pub.ids.length≤64)
    (ht:bs.Pairwise (fun a b=>a.run.tau≠b.run.tau)) : Chain (allRows bs) := by
  induction bs with
  | nil=>trivial
  | cons b bs ih=>
    obtain ⟨htail,hpair⟩:=List.pairwise_cons.mp ht
    change Chain (tagged b++allRows bs)
    apply chain_append _ _ (tagged_chain b) (ih (fun b hm=>hn b (by simp [hm])) hpair)
    intro a ha c hc
    have hbefore:=all_first bs c hc
    have hc_mem:c∈allRows bs:=List.mem_iff_getElem?.mpr ⟨0,hc⟩
    obtain ⟨d,hd,hcd⟩:=List.mem_flatMap.mp hc_mem
    have hba:=tagged_member b a ha
    have hdc:=tagged_member d c hcd
    have hal:=ProcPriorIndexed.row_bound _ _ (hn b (by simp)) a.row hba.2
    have hcl:=ProcPriorIndexed.row_bound _ _ (hn d (by simp [hd])) c.row hdc.2
    have hneq:address a≠address c := by
      intro he
      have hτ:=htail d hd
      unfold address at he
      rw [hba.1,hdc.1] at he
      omega
    exact ⟨by simpa only [ite_eq_right hneq] using hbefore,fun _=>hneq⟩
end ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
