import ZkFormal.NearV3.Qv.Candidates.EmptyRender

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec

/-- Fixed-size blocks can be indexed without assuming anything about their contents. -/
theorem flatMap_get_fixed {α β : Type} (xs : List α) (f : α → List β)
    (da : α) (db : β) (m i j : Nat)
    (hs : ∀ x ∈ xs, (f x).length = m) (hi : i < xs.length) (hj : j < m) :
    (xs.flatMap f).getD (m*i+j) db = (f (xs.getD i da)).getD j db := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    have hx := hs x (by simp)
    have ht : ∀ a ∈ xs, (f a).length=m := by intro a ha; exact hs a (by simp [ha])
    cases i with
    | zero =>
      simp only [List.flatMap_cons,Nat.mul_zero,Nat.zero_add]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left (by omega : j<(f x).length)]
      simp
    | succ i =>
      have hb : (f x).length ≤ m*(i+1)+j := by rw [hx,Nat.mul_add,Nat.mul_one]; omega
      simp only [List.flatMap_cons,List.getD_eq_getElem?_getD,List.getElem?_append_right hb]
      rw [← List.getD_eq_getElem?_getD]
      have he : m*(i+1)+j-(f x).length=m*i+j := by rw [hx,Nat.mul_add,Nat.mul_one]; omega
      rw [he,ih i ht (by simpa using hi)]
      simp

def bufferEntryRows (cfg : Config) (e : ByteBuffer) (i : Nat) : List (List Nat) :=
  wordRows cfg (4+24*i) 1 i e.shard e.index ++
  wordRows cfg (12+24*i) 2 i e.index e.index ++
  wordRows cfg (20+24*i) 3 i e.index e.index

@[simp] theorem bufferEntryRows_length (cfg : Config) (e : ByteBuffer) (i : Nat)
    (he : e.Sized) : (bufferEntryRows cfg e i).length=24 := by
  simp [bufferEntryRows,he.1,he.2]

theorem bufferEntryRows_get (cfg : Config) (e : ByteBuffer) (i j : Nat)
    (he : e.Sized) (hj : j<24) :
    (bufferEntryRows cfg e i).getD j [] =
      row cfg (4+24*i+j)
        ((if j<8 then e.shard.getD j 0 else e.index.getD (j%8) 0).toNat)
        (if j<8 then 1 else if j<16 then 2 else 3) (j%8) i e.index := by
  have hsh := he.1
  have hix := he.2
  unfold bufferEntryRows
  by_cases h8 : j<8
  · have hl : j<(wordRows cfg (4+24*i) 1 i e.shard e.index ++
        wordRows cfg (12+24*i) 2 i e.index e.index).length := by simp [he.1,he.2]; omega
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hl]
    rw [List.getElem?_append_left (by simpa [he.1] using h8)]
    rw [← List.getD_eq_getElem?_getD,wordRows_get _ _ _ _ _ _ (by omega)]
    simp [h8,Nat.mod_eq_of_lt h8]
  · by_cases h16 : j<16
    · have hl : j<(wordRows cfg (4+24*i) 1 i e.shard e.index ++
          wordRows cfg (12+24*i) 2 i e.index e.index).length := by simp [he.1,he.2]; omega
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hl]
      rw [List.getElem?_append_right (by simp [he.1]; omega)]
      simp only [wordRows_length,he.1]
      rw [← List.getD_eq_getElem?_getD,wordRows_get _ _ _ _ _ _ (by omega)]
      have hm : j%8=j-8 := by omega
      simp [h8,h16,hm,show 12+24*i+(j-8)=4+24*i+j by omega]
    · have hl : (wordRows cfg (4+24*i) 1 i e.shard e.index ++
          wordRows cfg (12+24*i) 2 i e.index e.index).length ≤ j := by simp [he.1,he.2]; omega
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right hl,
        List.length_append,wordRows_length,he.1,he.2]
      rw [← List.getD_eq_getElem?_getD,wordRows_get _ _ _ _ _ _ (by omega)]
      have hm : j%8=j-16 := by omega
      simp [h8,h16,hm,show 20+24*i+(j-16)=4+24*i+j by omega]

theorem flatMap_length_fixed {α β : Type} (xs : List α) (f : α → List β) (m : Nat)
    (hs : ∀ x ∈ xs, (f x).length=m) : (xs.flatMap f).length=m*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hs x (by simp)
    have ht : ∀ a ∈ xs, (f a).length=m := by intro a ha; exact hs a (by simp [ha])
    simp [hx,ih ht,Nat.mul_add,Nat.add_comm]

theorem bufferRows_length (vid tau users : Nat) (es : List ByteBuffer)
    (hs : ∀ e ∈ es, e.Sized) : (bufferRows vid tau users es).length=4+24*es.length := by
  let cfg : Config := ⟨vid,tau,users,1,4+24*es.length,es.length⟩
  have he : ∀ p ∈ es.zipIdx, (bufferEntryRows cfg p.1 p.2).length=24 := by
    rintro ⟨e,i⟩ hm
    exact bufferEntryRows_length cfg e i (hs e (List.fst_mem_of_mem_zipIdx hm))
  have hl := flatMap_length_fixed es.zipIdx (fun p => bufferEntryRows cfg p.1 p.2) 24 he
  simpa [bufferRows,bufferEntryRows,cfg,u32,leN] using hl

theorem bufferRows_header_get (vid tau users : Nat) (es : List ByteBuffer)
    (r : Nat) (hr : r<4) :
    (bufferRows vid tau users es).getD r [] =
      row ⟨vid,tau,users,1,4+24*es.length,es.length⟩ r
        ((u32 es.length).getD r 0).toNat 0 r 0 (u32 es.length) := by
  unfold bufferRows
  have hl : r<(wordRows ⟨vid,tau,users,1,4+24*es.length,es.length⟩ 0 0 0
      (u32 es.length) (u32 es.length)).length := by simpa [u32,leN] using hr
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hl]
  rw [← List.getD_eq_getElem?_getD,wordRows_get _ _ _ _ _ _ (by simpa [u32,leN] using hr)]
  simp

theorem bufferRows_entry_get (vid tau users : Nat) (es : List ByteBuffer)
    (hs : ∀ e ∈ es, e.Sized) (i j : Nat) (hi : i<es.length) (hj : j<24) :
    (bufferRows vid tau users es).getD (4+24*i+j) [] =
      (bufferEntryRows ⟨vid,tau,users,1,4+24*es.length,es.length⟩
        (es.getD i ⟨[],[]⟩) i).getD j [] := by
  let cfg : Config := ⟨vid,tau,users,1,4+24*es.length,es.length⟩
  have he : ∀ p ∈ es.zipIdx, (bufferEntryRows cfg p.1 p.2).length=24 := by
    rintro ⟨e,k⟩ hm
    exact bufferEntryRows_length cfg e k (hs e (List.fst_mem_of_mem_zipIdx hm))
  have hg := flatMap_get_fixed es.zipIdx (fun p => bufferEntryRows cfg p.1 p.2)
    (⟨[],[]⟩,0) [] 24 i j he (by simpa using hi) hj
  have hl : (wordRows cfg 0 0 0 (u32 es.length) (u32 es.length)).length ≤ 4+24*i+j := by
    simp [u32,leN]; omega
  unfold bufferRows
  change ((wordRows cfg 0 0 0 (u32 es.length) (u32 es.length)) ++
    es.zipIdx.flatMap (fun p => bufferEntryRows cfg p.1 p.2)).getD (4+24*i+j) [] = _
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right hl]
  rw [← List.getD_eq_getElem?_getD]
  have hh : (wordRows cfg 0 0 0 (u32 es.length) (u32 es.length)).length=4 := by simp [u32,leN]
  rw [hh,show 4+24*i+j-4=24*i+j by omega,hg]
  simp [List.getElem?_eq_getElem hi,cfg]

/-- Pointwise row formula, including all padding positions. -/
def bufferRowAt (vid tau users : Nat) (es : List ByteBuffer) (r : Nat) : List Nat :=
  let cfg : Config := ⟨vid,tau,users,1,4+24*es.length,es.length⟩
  if r<4 then row cfg r ((u32 es.length).getD r 0).toNat 0 r 0 (u32 es.length)
  else if r<4+24*es.length then
    let i := (r-4)/24
    let j := (r-4)%24
    let e := es.getD i ⟨[],[]⟩
    row cfg (4+24*i+j)
      ((if j<8 then e.shard.getD j 0 else e.index.getD (j%8) 0).toNat)
      (if j<8 then 1 else if j<16 then 2 else 3) (j%8) i e.index
  else []

theorem bufferRows_get (vid tau users : Nat) (es : List ByteBuffer)
    (hs : ∀ e ∈ es, e.Sized) (r : Nat) :
    (bufferRows vid tau users es).getD r [] = bufferRowAt vid tau users es r := by
  by_cases h4 : r<4
  · simpa [bufferRowAt,h4] using bufferRows_header_get vid tau users es r h4
  · by_cases hr : r<4+24*es.length
    · have hi : (r-4)/24<es.length := by omega
      have hj : (r-4)%24<24 := by omega
      have hd : 4+24*((r-4)/24)+(r-4)%24=r := by omega
      have he : (es.getD ((r-4)/24) ⟨[],[]⟩).Sized := by
        apply hs
        simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
      have hg := bufferRows_entry_get vid tau users es hs ((r-4)/24) ((r-4)%24) hi hj
      rw [hd] at hg
      rw [hg,bufferEntryRows_get _ _ _ _ he hj]
      simp [bufferRowAt,h4,hr]
    · have hn : (bufferRows vid tau users es).length ≤ r := by rw [bufferRows_length _ _ _ _ hs]; omega
      simp [bufferRowAt,h4,hr,List.getD_eq_getElem?_getD,List.getElem?_eq_none hn]

end ZkFormal.NearV3.Qv.Candidates.ValueGen
