import ZkFormal.NearV3.Rcpt.Candidates.SourcePrepared

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec
open NearSpecV3 (SrcList Prep Hint ProofEntry)

/-- Every extracted block has its actual repetition annotation in the view list. -/
theorem sourceViews_mem {tr : Trace Fp} {tt s : Nat} {bs : List SrcpB} {B : SrcpB}
    (hB : B∈bs) : ∃ rep, (B,rep)∈sourceViews tr tt s bs := by
  rw [← sourceViews_blocks tr tt s bs] at hB
  obtain ⟨⟨C, rep⟩, hm, he⟩ := List.mem_map.mp hB
  cases he
  exact ⟨rep, hm⟩

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

theorem BlockChain.bind_prepared {stop : Nat} {bs : List SrcpB}
    (hc : BlockChain tr tt 0 bs stop) {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : NearSpecV3.prepD0 cb hint=.ok p)
    (hbal : ∀ m, cnt (sourceMsgs tr tt bs B_SRC false) m=cnt (SourcePublic.records p.lists) m) :
    bs.length=p.lists.length ∧
    ∀ v∈sourceViews tr tt 0 bs,
      v.1.j<p.lists.length ∧ v.1.dup=Public.sourceDup p.lists v.1.j ∧
      v.2=sourceRepeated p.lists v.1.j ∧
      toBytes v.1.root=(p.lists.getD v.1.j ⟨[],0,[]⟩).root ∧
      (sourceRepeated p.lists v.1.j=true → v.1.L=12) := by
  have hh := prepD0_source_count hp
  exact hc.bind_public hL p.lists (by unfold P; omega) hbal

/-- SHA-authenticated first occurrences and the concrete candidate preparation
check authenticate the whole last-wins source dictionary, including every skip.
RC digest/dictionary/path binding is stated explicitly as `hentries`. -/
theorem BlockChain.sources_authenticated {stop : Nat} {bs : List SrcpB}
    (hc : BlockChain tr tt 0 bs stop) {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepSourceD0 cb hint=.ok p) (entries : List ProofEntry) (own : Nat)
    (hpub : ∀ m, cnt (sourceMsgs tr tt bs B_SRC false) m=cnt (SourcePublic.records p.lists) m)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR) (others : List Msg)
    (hbytes : ∀ m, shaR B_BYTES m=cnt (sourceMsgs tr tt bs B_BYTES true++others) m)
    (hother : ∀ m∈others, ∀ a, m.head?=some a → a<P ∧ a%16≠K_SRC)
    (hdigest : ∀ m∈sourceMsgs tr tt bs B_DIGEST false, 0<shaS B_DIGEST m.toFp)
    (hentries : ∀ B∈bs, B.dup=false → ∃ e,
      NearSpecV3.lookupLast (p.lists.getD B.j ⟨[],0,[]⟩).key entries=some e ∧
      e.proof.fromShard=(p.lists.getD B.j ⟨[],0,[]⟩).fromShard ∧ e.proof.toShard=own ∧
      toBytes B.leaf=sha256 (u64 e.proof.toShard++encodeReceipts e.receipts) ∧
      e.proof.path=B.path.map SrcpItem.proofStep) :
    ∀ s∈p.lists, PreparedSourceAuthenticated entries own s := by
  obtain ⟨hprep, hmeta⟩ := prepSourceD0_sound hp
  have hb := hc.bind_prepared hL hprep hpub
  apply sources_authenticated_of_first p.lists entries own hmeta
  intro i hi hd
  have hbi : i<bs.length := by omega
  let B := bs[i]
  have hBm : B∈bs := List.getElem_mem hbi
  obtain ⟨rep, hrep⟩ := sourceViews_mem (tr := tr) (tt := tt) (s := 0) hBm
  have hf := hb.2 (B,rep) hrep
  have hj : B.j=i := by
    have hh := hc.j_indices hL i hbi
    rw [(row0 hL).2.1] at hh
    simpa only [show Fp.toNat 0=0 from rfl, Nat.zero_add] using hh
  have hdup : B.dup=false := by rw [hf.2.1, hj, hd]
  obtain ⟨e, he, hfrom, hto, hleaf, hpath⟩ := hentries B hBm hdup
  have hv := hc.verifyReceiptProof hL hsha others hbytes hother hdigest hBm hdup e hleaf hpath
  rw [hf.2.2.2.1, hj] at hv
  exact ⟨e, by simpa only [hj] using he, by simpa only [hj] using hfrom, hto, hv⟩

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
