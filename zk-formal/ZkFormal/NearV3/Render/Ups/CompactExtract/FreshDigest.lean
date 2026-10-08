import ZkFormal.NearV3.Render.Ups.CompactExtract.TableTraffic
import ZkFormal.NearV3.Render.Ups.RelayNativeInventory
import ZkFormal.NearV3.Extract.Ups.UpsBus
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open NearSpec Assembly ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows UpsGen

theorem digest_member {C D : URow} (hC : ∀x,C x<P) (hg : C gD=1) :
    [C dI,C dL]++regN C∈uMsgs C D B_DIGEST false := by
  apply List.mem_flatMap.mpr
  refine ⟨recv B_DIGEST (c gD) ([c dI,c dL]++regs),by simp [UpsV3.interactions],?_⟩
  have hm : uMult C D (recv B_DIGEST (c gD) ([c dI,c dL]++regs))=1 := by
    simp [uMult,Dsl.recv,uev,Expr.evalWith,uEnv,Dsl.c,hg,UpsRows.cast_ofNat,UpsRows.cast1]
  rw [ite_eq_left (by exact ⟨rfl,rfl⟩),hm]
  simp only [List.replicate_one,List.mem_singleton]
  simp [Dsl.recv,regs,regN,List.map_append,List.map_map,uev,Expr.evalWith,uEnv,Dsl.c,
    Fp.toNat_ofNat,Nat.mod_eq_of_lt (hC _),Function.comp_def]

/-- Fresh-value digest authenticity on the ACTUAL extracted compact view.
The remaining global premises are SHA bus balance/ownership and digest matching,
not a desired hash equality or unconstrained byte lookup. -/
theorem fresh_digest {v : List UpsSeg} (hw : Wf v)
    {shaS shaR : Nat→List Fp→Nat} (hsha : ShaFacts shaS shaR)
    (taus : List Nat) (values : Nat→Bytes) (nodes : List ZkFormal.Sha.Gen.Msg) (others : List Msg)
    (htaus : ∀tau∈taus,tau<32)
    (hnodes : ∀M∈nodes,∃tau j,tau<32 ∧ 1≤j ∧ j<512 ∧ M.id=upsertJobId tau j)
    (hothers : ∀m∈others,∀a,m.head?=some a → a<P ∧ a%16≠K_VUPS)
    (hbytes : ∀m,shaR B_BYTES m=cnt (relayInventory taus values nodes others) m)
    (hdig : ∀m∈(upsTraffic v).recvs B_DIGEST,0<shaS B_DIGEST m.toFp)
    {s : UpsSeg} (hs : s∈v) {i tau : Nat} (hi : i<s.rows.length)
    (ht : tau<32) (hlen : (values tau).length<2^24)
    (hg : s.row i gD=1) (hid : s.row i dI=upsertJobId tau 0)
    (hl : s.row i dL=(values tau).length) :
    regN (s.row i)=(sha256 (values tau)).map UInt8.toNat := by
  apply relay_fresh_digest hsha taus values nodes others htaus hnodes hothers hbytes ht hlen
  · intro b hb
    obtain ⟨x,_,rfl⟩:=List.mem_map.mp hb
    exact rowLt hw hs _ _
  · have hm:=digest_member (D:=s.next i) (rowLt hw hs i) hg
    have hh:=hdig _ (mem_upsRecvs.mpr ⟨s,hs,i,hi,hm⟩)
    simpa only [hid,hl,digMsg] using hh
end ZkFormal.NearV3.Render.UpsRelay.Extract
