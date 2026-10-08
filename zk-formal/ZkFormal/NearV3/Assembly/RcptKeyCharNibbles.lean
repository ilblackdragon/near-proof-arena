import ZkFormal.NearV3.Assembly.RcptKeyPkBits

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

theorem keyByte_character (p : ReceiptPlan) (row : Coord) (hs : row.state=sV ∨ row.state=sS) :
    keyByte p row=characterByte p row := by
  rcases hs with hs|hs <;> simp only [keyByte,characterByte,characterBytes,hs,sV,sS,sP,sPK,Nat.reduceEqDiff,ite_true,ite_false]

theorem eval_key_bits (tr : Trace Fp) (t pos : Nat) (pub : List Fp) (cols : Nat→Nat)
    (x len : Nat) (hc : ∀j,j<len→tr.cell t pos (cols j)=frameBit x j) :
    (bits (fun j=>c (cols j)) 0 len).eval tr t pos pub=Fp.ofNat (x%2^len) := by
  have hh : (bits (fun j=>c (cols j)) 0 len).eval tr t pos pub=Fp.ofNat (bitsVal (fun j=>(x/2^j)%2) 0 len) := by
    induction len with
    | zero => rfl
    | succ len ih =>
      rw [bits_succ,eval_sum_append]
      change (bits (fun j=>c (cols j)) 0 len).eval tr t pos pub+_=_
      rw [ih (fun j hj=>hc j (by omega))]
      simp only [eval_sum_cons,eval_sum_nil,eval_smul,eval_c,Nat.zero_add,hc len (by omega),frameBit,bitsVal]
      change (↑(bitsVal (fun j=>(x/2^j)%2) 0 len):Fp) + ((↑(2^len:Nat):Fp) * ↑((x/2^len)%2)+0) = ↑(bitsVal (fun j=>(x/2^j)%2) 0 len + 2^len*((x/2^len)%2))
      simp only [natCast_add,natCast_mul]
      grind only
  rw [hh,frame_bitsVal]

theorem key_character_nibbles (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (hw : p.input.receipt.wf=true) (hs : row.state=sV ∨ row.state=sS)
    (hi : row.index<fieldLen p.input row.state) :
    let tr := receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (characterAux fallback))) p row row
    hiE.eval tr 0 0 pub=Fp.ofNat (keyByte p row/16) ∧
      loE.eval tr 0 0 pub=Fp.ofNat (keyByte p row%16) := by
  let tr := receiptPair (booleanConstants constants)
    (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (characterAux fallback))) p row row
  have hss : row.state∈[sP,sV,sS] := by simp only [List.mem_cons,List.not_mem_nil,or_false];grind only
  have hc := character_receipt_cells ctx lists constants pub digests fallback p row hss
  have hb := keyByte_character p row hs
  have hh := hi_char (characterByte p row) (characterByte_lt p row) (characterByte_valid p row hw hss hi)
  change hiE.eval tr 0 0 pub=_ ∧ loE.eval tr 0 0 pub=_
  constructor
  · have he (col : Nat) (hcol : col∈[h2,h3,h5,h6,h7]) : tr.cell 0 0 col=Fp.ofNat (charCell (characterByte p row) col) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hcol
      rcases hcol with rfl|rfl|rfl|rfl|rfl
      · exact (hc h2 (by decide)).trans rfl
      · exact (hc h3 (by decide)).trans rfl
      · exact (hc h5 (by decide)).trans rfl
      · exact (hc h6 (by decide)).trans rfl
      · exact (hc h7 (by decide)).trans rfl
    simp only [hiE,eval_sum_cons,eval_sum_nil,eval_smul,eval_c,he h2 (by decide),he h3 (by decide),
      he h5 (by decide),he h6 (by decide),he h7 (by decide),hb]
    have hcast := congrArg Fp.ofNat hh
    simp only [ofNat_add_e,ofNat_mul_e] at hcast
    change _=Fp.ofNat (characterByte p row/16)
    simp only [h2,h3,h5,h6,h7]
    rw [hcast]
    simp only [show Fp.ofNat 2=(2:Fp) from rfl,show Fp.ofNat 3=(3:Fp) from rfl,show Fp.ofNat 5=(5:Fp) from rfl,show Fp.ofNat 6=(6:Fp) from rfl,show Fp.ofNat 7=(7:Fp) from rfl]
    grind only
  · have he (j : Nat) (hj : j<4) : tr.cell 0 0 (lb j)=frameBit (characterByte p row%16) j := by
      have hj' : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
      rcases hj' with rfl|rfl|rfl|rfl
      · exact (hc (lb 0) (by decide)).trans rfl
      · exact (hc (lb 1) (by decide)).trans rfl
      · exact (hc (lb 2) (by decide)).trans rfl
      · exact (hc (lb 3) (by decide)).trans rfl
    rw [show loE=bits (fun j=>c (lb j)) 0 4 from rfl,eval_key_bits tr 0 0 pub lb _ _ he,
      Nat.mod_eq_of_lt (show characterByte p row%16<2^4 from Nat.mod_lt _ (by decide)),hb]

end ZkFormal.NearV3.Assembly.RcptSkeleton
