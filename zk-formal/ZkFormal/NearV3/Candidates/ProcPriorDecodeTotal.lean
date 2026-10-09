import ZkFormal.NearV3.Candidates.ProcPriorDecode
namespace ZkFormal.NearV3.Candidates.ProcPriorDecodeTotal
open NearSpec NearSpec.Bandwidth

/-- Fixed-width reads succeed on every sufficiently long byte string. -/
theorem take_total (n:Nat) (bs:Bytes) (hn:n≤bs.length) :
    ∃head rest,takeN n bs=some (head,rest) ∧ head.length=n ∧ rest.length=bs.length-n := by
  induction n generalizing bs with
  | zero=>exact ⟨[],bs,rfl,rfl,by omega⟩
  | succ n ih=>
    cases bs with
    | nil=>simp at hn
    | cons b bs=>
      obtain ⟨head,rest,he,hl,hr⟩:=ih bs (by simp only [List.length_cons] at hn;omega)
      refine ⟨b::head,rest,?_,by simp [hl],?_⟩
      · simp [takeN,he]
      · simp only [List.length_cons];omega

theorem read_total (n:Nat) (bs:Bytes) (hn:n≤bs.length) :
    ∃x rest,readLE n bs=some (x,rest) ∧ rest.length=bs.length-n := by
  obtain ⟨head,rest,he,_,hr⟩:=take_total n bs hn
  exact ⟨leNat head,rest,by simp [readLE,he],hr⟩

theorem link_total (bs:Bytes) (hn:24≤bs.length) :
    ∃link rest,readLink bs=some (link,rest) ∧ rest.length=bs.length-24 := by
  obtain ⟨s,b1,h1,l1⟩:=read_total 8 bs (by omega)
  obtain ⟨r,b2,h2,l2⟩:=read_total 8 b1 (by omega)
  obtain ⟨a,rest,h3,l3⟩:=read_total 8 b2 (by omega)
  exact ⟨⟨s,r,a⟩,rest,by simp [readLink,readU64,h1,h2,h3],by omega⟩

theorem links_total (n:Nat) (bs:Bytes) (hn:24*n≤bs.length) :
    ∃links rest,readMany readLink n bs=some (links,rest) ∧
      links.length=n ∧ rest.length=bs.length-24*n := by
  induction n generalizing bs with
  | zero=>exact ⟨[],bs,rfl,rfl,by omega⟩
  | succ n ih=>
    obtain ⟨link,b1,h1,l1⟩:=link_total bs (by omega)
    obtain ⟨links,rest,h2,l2,l3⟩:=ih b1 (by omega)
    exact ⟨link::links,rest,by simp [readMany,h1,h2],by simp [l2],by omega⟩

/-- Native decoding succeeds once the tag/count header and exact remaining
length are established; record contents require no additional validity premise. -/
theorem decode_total (bs afterTag payload:Bytes) (n:Nat)
    (hTag:readU8 bs=some (0,afterTag))
    (hCount:readU32 afterTag=some (n,payload))
    (hlen:payload.length=24*n+32) :
    ∃st,State.decode bs=some st ∧ st.links.length=n ∧ st.sanityHash.length=32 := by
  obtain ⟨links,hash,hr,hl,hrest⟩:=links_total n payload (by omega)
  have hhash:hash.length=32:=by omega
  obtain ⟨head,rest,hh,hhead,hend⟩:=take_total 32 hash (by omega)
  have hempty:rest=[]:=by
    cases rest with
    | nil=>rfl
    | cons a rest=>simp only [List.length_cons] at hend;omega
  subst rest
  refine ⟨⟨links,head⟩,?_,hl,hhead⟩
  simp [State.decode,hTag,hCount,hr,readHash,hh]
theorem framed_decode (bs:Bytes) (n:Nat)
    (hlen:bs.length=37+24*n)
    (hzero:(bs.getD 0 0).toNat=0) (hhigh:(bs.getD 4 0).toNat=0)
    (hcount:n=(bs.getD 1 0).toNat+256*(bs.getD 2 0).toNat+65536*(bs.getD 3 0).toNat) :
    ∃st,State.decode bs=some st ∧ st.links.length=n ∧ st.sanityHash.length=32 := by
  cases bs with
  | nil=>simp at hlen;omega
  | cons b0 bs=>
    cases bs with
    | nil=>simp at hlen;omega
    | cons b1 bs=>
      cases bs with
      | nil=>simp at hlen;omega
      | cons b2 bs=>
        cases bs with
        | nil=>simp at hlen;omega
        | cons b3 bs=>
          cases bs with
          | nil=>simp at hlen;omega
          | cons b4 payload=>
            simp only [List.getD_cons_zero,List.getD_cons_succ] at hzero hhigh hcount
            apply decode_total _ (b1::b2::b3::b4::payload) payload n
            · simp [readU8,readLE,takeN,leNat,hzero]
            · simp [readU32,readLE,takeN,leNat,hhigh]
              omega
            · simp only [List.length_cons] at hlen
              omega
theorem nat_framed_decode (data:List Nat) (n:Nat)
    (hbytes:∀x∈data,x<256) (hlen:data.length=37+24*n)
    (hzero:data.getD 0 0=0) (hhigh:data.getD 4 0=0)
    (hcount:n=data.getD 1 0+256*data.getD 2 0+65536*data.getD 3 0) :
    ∃bs:Bytes,∃st,bs.map UInt8.toNat=data ∧ State.decode bs=some st ∧
      st.links.length=n ∧ st.sanityHash.length=32 := by
  let bs:Bytes:=data.map UInt8.ofNat
  have hmap:bs.map UInt8.toNat=data:=by
    change (data.map UInt8.ofNat).map UInt8.toNat=data
    rw [List.map_map]
    have he: data.map (UInt8.toNat ∘ UInt8.ofNat)=data.map id:=by
      apply List.map_congr_left
      intro x hx
      change (UInt8.ofNat x).toNat=x
      simp only [UInt8.toNat_ofNat']
      exact Nat.mod_eq_of_lt (hbytes x hx)
    exact he.trans (List.map_id data)
  have hget (j:Nat):(bs.getD j 0).toNat=data.getD j 0:=by
    have h:=congrArg (fun xs:List Nat=>xs.getD j 0) hmap
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map] at h ⊢
    cases he:bs[j]? with
    | none=>simpa [he] using h
    | some b=>simpa [he] using h
  have hlength:bs.length=37+24*n:=by simpa only [bs,List.length_map] using hlen
  obtain ⟨st,hd,hl,hh⟩:=framed_decode bs n hlength
    ((hget 0).trans hzero) ((hget 4).trans hhigh) (by simpa only [hget] using hcount)
  exact ⟨bs,st,hmap,hd,hl,hh⟩
end ZkFormal.NearV3.Candidates.ProcPriorDecodeTotal
