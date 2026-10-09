import ZkFormal.NearV3.Render.Ups.CodecRelayTraffic
import ZkFormal.NearV3.Sched.Link.CodecSV
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Sched

def codecFirstRows (tr : Trace Fp) (t : Nat) : List Nat :=
  (List.range (tr.height t)).filter fun f=>ZkFormal.Chacha.cv tr t f Codec.kF==1

def codecEncodingRows (tr : Trace Fp) (t : Nat) : List Nat :=
  (List.range (tr.height t)).filter fun r=>
    ZkFormal.Chacha.cv tr t r Codec.kH+ZkFormal.Chacha.cv tr t r Codec.kR+ZkFormal.Chacha.cv tr t r Codec.kZ==1

def codecBlockRows (tr : Trace Fp) (t f : Nat) : List Nat :=
  (List.range (37+24*ZkFormal.Chacha.cv tr t f Codec.NN)).map (f+·)

private theorem first_mem {tr : Trace Fp} {t f : Nat} :
    f∈codecFirstRows tr t ↔ f<tr.height t ∧ ZkFormal.Chacha.cv tr t f Codec.kF=1 := by
  simp [codecFirstRows]

private theorem block_mem {tr : Trace Fp} {t f r : Nat} :
    r∈codecBlockRows tr t f ↔ ∃p,p<37+24*ZkFormal.Chacha.cv tr t f Codec.NN ∧ f+p=r := by
  simp [codecBlockRows]

/-- Position registers determine the physical first row uniquely. This proves
blocks do not overlap without any assumed instance-ID uniqueness. -/
theorem codecBlockRows_disjoint {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    {f g r : Nat} (hf : f∈codecFirstRows tr t) (hg : g∈codecFirstRows tr t)
    (hr : r∈codecBlockRows tr t f) (hs : r∈codecBlockRows tr t g) : f=g := by
  obtain ⟨hf,hF⟩:=first_mem.mp hf
  obtain ⟨hg,hG⟩:=first_mem.mp hg
  obtain ⟨p,hp,he⟩:=block_mem.mp hr
  obtain ⟨q,hq,hq'⟩:=block_mem.mp hs
  have ep := (Codec.enc_rows hl hh hf hF p (by omega)).2.2.1
  have eq := (Codec.enc_rows hl hh hg hG q (by omega)).2.2.1
  rw [he] at ep
  rw [hq'] at eq
  omega

/-- Every encoding row belongs to one real codec block, and conversely. -/
theorem codecEncodingRows_mem {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22) (r : Nat) :
    r∈codecEncodingRows tr t ↔
      r∈(codecFirstRows tr t).flatMap (codecBlockRows tr t) := by
  simp only [List.mem_flatMap]
  constructor
  · intro hr
    have hr' : r<tr.height t ∧ ZkFormal.Chacha.cv tr t r Codec.kH+ZkFormal.Chacha.cv tr t r Codec.kR+ZkFormal.Chacha.cv tr t r Codec.kZ=1 := by
      simpa [codecEncodingRows] using hr
    obtain ⟨f,hfr,hF,hp⟩:=Codec.enc_row hl hh hr'.1 hr'.2
    exact ⟨f,first_mem.mpr ⟨by omega,hF⟩,block_mem.mpr ⟨r-f,hp,by omega⟩⟩
  · rintro ⟨f,hf,hr⟩
    obtain ⟨hf,hF⟩:=first_mem.mp hf
    obtain ⟨p,hp,rfl⟩:=block_mem.mp hr
    have he:=Codec.enc_rows hl hh hf hF p (by omega)
    simpa [codecEncodingRows] using And.intro he.1 he.2.1
private theorem flatMap_nodup {α β : Type} (f : α→List β) :
    ∀ (xs : List α), xs.Nodup → (∀a∈xs,(f a).Nodup) →
    (∀a∈xs,∀b∈xs,∀r,r∈f a → r∈f b → a=b) → (xs.flatMap f).Nodup
  | [],_,_,_ => by simp
  | a::xs,hn,hf,hd => by
    rw [List.nodup_cons] at hn
    rw [List.flatMap_cons,List.nodup_append]
    refine ⟨hf a (by simp),flatMap_nodup f xs hn.2 (fun b hb=>hf b (by simp [hb]))
      (fun b hb c hc=>hd b (by simp [hb]) c (by simp [hc])),?_⟩
    intro r hr z hz he
    subst z
    obtain ⟨b,hb,hrb⟩:=List.mem_flatMap.mp hz
    have hab:=hd a (by simp) b (by simp [hb]) r hr hrb
    exact hn.1 (hab ▸ hb)

theorem codecEncodingRows_perm {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22) :
    (codecEncodingRows tr t).Perm ((codecFirstRows tr t).flatMap (codecBlockRows tr t)) := by
  have he : (codecEncodingRows tr t).Nodup := List.nodup_range.filter _
  have hf : (codecFirstRows tr t).Nodup := List.nodup_range.filter _
  have hn : ((codecFirstRows tr t).flatMap (codecBlockRows tr t)).Nodup := by
    apply flatMap_nodup _ _ hf
    · intro f _
      exact ZkFormal.Algebra.nodup_map_on (fun a _ b _ he => by omega) List.nodup_range
    · intro f hf g hg r hr hs
      exact codecBlockRows_disjoint hl hh hf hg hr hs
  exact (List.perm_ext_iff_of_nodup he hn).mpr (codecEncodingRows_mem hl hh)
end ZkFormal.NearV3.Render.UpsRelay
