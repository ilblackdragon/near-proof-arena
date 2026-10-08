import ZkFormal.NearV3.Candidates.ProcPriorLookup
import ZkFormal.Near.Spec.SoundAccount
namespace ZkFormal.NearV3.Candidates.ProcPriorDecode
open NearSpec NearSpec.Bandwidth ZkFormal.NearV3.Sched

theorem take_exact (n : Nat) (bs v rest : Bytes) (h : takeN n bs=some (v,rest)) :
    v.length=n ∧ bs=v++rest := by
  induction n generalizing bs v with
  | zero => cases h; simp
  | succ n ih =>
    cases bs with
    | nil => simp [takeN] at h
    | cons b bs =>
      simp only [takeN,Option.map_eq_some_iff] at h
      obtain ⟨⟨v',r'⟩,hh,he⟩:=h
      cases he
      obtain ⟨hl,hb⟩:=ih bs v' hh
      simp [hl,hb]

theorem readLE_exact (n : Nat) (bs rest : Bytes) (v : Nat)
    (h : readLE n bs=some (v,rest)) : v<256^n ∧ bs=leN n v++rest := by
  simp only [readLE,Option.map_eq_some_iff] at h
  obtain ⟨⟨v',r'⟩,hh,he⟩:=h
  cases he
  obtain ⟨hl,hb⟩:=take_exact n bs v' r' hh
  have ht:=ZkFormal.Near.Sound.leNat_lt v'
  have he:=ZkFormal.Near.Sound.leN_leNat v'
  rw [hl] at ht he
  exact ⟨ht,by simpa only [he] using hb⟩

theorem readLink_exact (bs rest : Bytes) (r : LinkAllowance)
    (h : readLink bs=some (r,rest)) : LinkOk r ∧ bs=r.encode++rest := by
  unfold readLink at h
  split at h
  · cases h
  next s b1 hs =>
    split at h
    · cases h
    next r' b2 hr =>
      split at h
      · cases h
      next a b3 ha =>
        cases h
        obtain ⟨hsl,hsb⟩:=readLE_exact 8 bs b1 s hs
        obtain ⟨hrl,hrb⟩:=readLE_exact 8 b1 b2 r' hr
        obtain ⟨hal,hab⟩:=readLE_exact 8 b2 rest a ha
        refine ⟨⟨hsl,hrl,hal⟩,?_⟩
        simp only [LinkAllowance.encode,u64,hsb,hrb,hab,List.append_assoc]

theorem readLinks_exact (n : Nat) (bs rest : Bytes) (rs : List LinkAllowance)
    (h : readMany readLink n bs=some (rs,rest)) :
    rs.length=n ∧ (∀ r∈rs,LinkOk r) ∧ bs=concatAll (rs.map LinkAllowance.encode)++rest := by
  induction n generalizing bs rs with
  | zero => cases h; simp [concatAll]
  | succ n ih =>
    unfold readMany at h
    split at h
    · cases h
    next r b1 hr =>
      split at h
      · cases h
      next rs' b2 hl =>
        cases h
        obtain ⟨hlen,hw,hb⟩:=ih b1 rs' hl
        obtain ⟨hw',hb'⟩:=readLink_exact bs b1 r hr
        refine ⟨by simp [hlen],?_,?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl|hx
          · exact hw'
          · exact hw x hx
        · simp [concatAll,hb',hb,List.append_assoc]

/-- Accepted decoding retains the exact original byte string, arbitrary record
count/order/IDs included. No normalization or canonical-layout premise. -/
theorem decode_exact (bs : Bytes) (st : State) (h : State.decode bs=some st) :
    st.links.length<2^32 ∧ (∀ r∈st.links,LinkOk r) ∧ st.sanityHash.length=32 ∧ bs=st.encode := by
  unfold State.decode at h
  split at h
  · cases h
  next tag b1 ht =>
    split at h
    · cases h
    next hz =>
      have hz':tag=0 := by omega
      subst tag
      split at h
      · cases h
      next n b2 hn =>
        split at h
        · cases h
        next rs b3 hl =>
          split at h
          · cases h
          next hash b4 hh =>
            split at h
            next hb4 =>
              subst b4
              cases h
              obtain ⟨_,htb⟩:=readLE_exact 1 bs b1 0 ht
              obtain ⟨hnl,hnb⟩:=readLE_exact 4 b1 b2 n hn
              obtain ⟨hrl,hw,hrb⟩:=readLinks_exact n b2 b3 rs hl
              obtain ⟨hhl,hhb⟩:=take_exact 32 b3 hash [] hh
              refine ⟨by simpa [hrl] using hnl,hw,hhl,?_⟩
              simp only [State.encode,u32,hrl,htb,hnb,hrb,hhb,leN,List.append_nil,List.append_assoc]
              rfl
            · cases h

theorem links_encoded_length (rs : List LinkAllowance) :
    (concatAll (rs.map LinkAllowance.encode)).length=24*rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [concatAll,LinkAllowance.encode,u64,canon_leN_length,ih]; omega

/-- Native prior count comes from the original bytes, not the current grid. -/
theorem decode_length (bs : Bytes) (st : State) (h : State.decode bs=some st) :
    bs.length=37+24*st.links.length := by
  obtain ⟨_,_,hh,he⟩:=decode_exact bs st h
  rw [he]
  simp [State.encode,links_encoded_length,u32,canon_leN_length,hh]
  omega

end ZkFormal.NearV3.Candidates.ProcPriorDecode
