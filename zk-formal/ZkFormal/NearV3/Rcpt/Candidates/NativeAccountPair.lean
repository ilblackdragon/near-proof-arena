import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountSignature
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near

theorem decoded_amount_prefix {post : Bytes} {a : Account} (hd:Account.decode post=some a) :
    u128 a.amount=post.take 16 := by
  rw [←Sound.encode_decode hd]
  simp [Account.encode,List.append_assoc,u128,leN_length]

/-- The honest closing record can use the exact final native account amount,
while its authenticated pre bytes stay those of the initial trie. -/
theorem nativeAccountView_final_payload (vid closing : Nat) {pre post : Bytes} {a : Account}
    (hd:Account.decode post=some a) (hs:post.drop 16=pre.drop 16) :
    (nativeAccountView vid closing pre a.amount).post++
      (nativeAccountView vid closing pre a.amount).pre.drop 16=post.map UInt8.toNat := by
  simp only [nativeAccountView,←List.map_drop]
  rw [decoded_amount_prefix hd,←hs,←List.map_append,List.take_append_drop]

/-- Signature conservation transports decodability from any actually decoded
later account back to the original occurrence, without assuming raw-byte equality. -/
theorem signature_decoded_before {pre post : Bytes} {a : Account}
    (he:accountSignature post=accountSignature pre) (hd:Account.decode post=some a) :
    ∃before,Account.decode pre=some before ∧ post.drop 16=pre.drop 16 := by
  have hb:=congrArg Prod.fst he
  have hs:=congrArg Prod.snd he
  simp only [accountSignature,hd,Option.isSome_some] at hb
  cases hp:Account.decode pre with
  | none=>simp [hp] at hb
  | some before=>exact ⟨before,rfl,hs⟩

/-- A chosen original/final occurrence pair yields a complete account record
and exact final SHA payload; byte fidelity is intrinsic to its constructor. -/
theorem nativeAccountPair_view (vid closing : Nat) (hk:vid<Algebra.P) (ht:closing<Algebra.P)
    {pre post : Bytes} {a : Account} (he:accountSignature post=accountSignature pre)
    (hd:Account.decode post=some a) :
    AcctWf [nativeAccountView vid closing pre a.amount] ∧
      (nativeAccountView vid closing pre a.amount).post++
        (nativeAccountView vid closing pre a.amount).pre.drop 16=post.map UInt8.toNat ∧
      ∀m∈accountShaJobs [nativeAccountView vid closing pre a.amount],∀b∈m.bytes,b<256 := by
  obtain ⟨before,hpre,hs⟩:=signature_decoded_before he hd
  exact ⟨nativeAccountView_wf vid closing hk ht hpre a.amount,
    nativeAccountView_final_payload vid closing hd hs,nativeAccountView_job_bytes vid closing pre a.amount⟩

/-- Actual sequential native execution supplies the signature of each same
compact value index, so no immutable-suffix premise is needed by its account view. -/
theorem native_execution_account_view {ctx : NearSpecV3.ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : TransferV1.Acc×List NearSpecV3.Limit}
    (hr:NearSpecV3.applyReceipts ctx i st rs=.ok out)
    {j : Nat} {pre post : Bytes} {a : Account}
    (hpre:(NearSpecV3.valsOf st.1.trie)[j]?=some pre)
    (hpost:(NearSpecV3.valsOf out.1.trie)[j]?=some post)
    (hd:Account.decode post=some a) (closing : Nat) (hk:j<Algebra.P) (ht:closing<Algebra.P) :
    AcctWf [nativeAccountView j closing pre a.amount] ∧
      (nativeAccountView j closing pre a.amount).post++
        (nativeAccountView j closing pre a.amount).pre.drop 16=post.map UInt8.toNat ∧
      ∀m∈accountShaJobs [nativeAccountView j closing pre a.amount],∀b∈m.bytes,b<256 := by
  have he:=congrArg (fun xs=>xs[j]?) (native_receipt_signatures ctx rs i st out hr)
  simp only [List.getElem?_map,hpre,hpost,Option.map_some,Option.some.injEq] at he
  exact nativeAccountPair_view j closing hk ht he hd

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
