import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowPatchedTraffic

namespace ZkFormal.NearV3.Candidates.WindowPatchOtherTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Rcpt.Candidates.NodePostUpdate Render.UpsRelay

private theorem bit_cell {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (h : TableLocal compactTable tr t pub) (hr : r<tr.height t)
    {c : Nat} (hc : c∈UpsV3.rowBools) : tr.cell t r c=0 ∨ tr.cell t r c=1 := by
  have he : Dsl.bool (Dsl.c c)∈compactTable.constraints := by
    have hm : Dsl.bool (Dsl.c c)∈UpsV3.cBool := by
      simp only [UpsV3.cBool,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false,or_assoc]
      exact Or.inl ⟨c,hc,rfl⟩
    simp [compactTable,compactConstraints,hm]
  have hh:=h.constr r hr _ he
  simp only [Dsl.bool,eval_mul,eval_sub,eval_c,eval_k] at hh
  rcases mul_eq_zero'.mp hh with hz|hz
  · exact Or.inl hz
  · right; grind

set_option maxHeartbeats 1000000 in
theorem reader_walk_gates {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (h : TableLocal compactTable tr t pub) (hr : r<tr.height t)
    (hd : tr.cell t r UpsV3.rd=1) :
    tr.cell t r UpsV3.mS=0 ∧ tr.cell t r UpsV3.mK=0 ∧ tr.cell t r UpsV3.mB=0 := by
  have get (e : Expr) (he : e∈compactTable.constraints) := h.constr r hr e he
  have hread:=get (.mul (Dsl.not (c UpsV3.qb)) (c UpsV3.rd)) (by simp [compactTable,compactConstraints,UpsV3.cBytes])
  have hrow:=get (sub (c UpsV3.act) (.add (c UpsV3.wk) (.add (c UpsV3.vb) (c UpsV3.qb)))) (by simp [compactTable,compactConstraints,compactRows,UpsV3.cRows])
  have hwalk:=get (.mul (sub (.add (c UpsV3.mS) (.add (c UpsV3.mK) (c UpsV3.mB))) (k 0)) (Dsl.not (c UpsV3.wk))) (by simp [compactTable,compactConstraints,UpsV3.cWalk])
  simp only [eval_mul,eval_sub,eval_not,eval_add,eval_c,eval_k,hd] at hread hrow hwalk
  have hq : tr.cell t r UpsV3.qb=1 := by grind
  have ha:=bit_cell h hr (c:=UpsV3.act) (by decide)
  have hw:=bit_cell h hr (c:=UpsV3.wk) (by decide)
  have hv:=bit_cell h hr (c:=UpsV3.vb) (by decide)
  have hs:=bit_cell h hr (c:=UpsV3.mS) (by decide)
  have hk:=bit_cell h hr (c:=UpsV3.mK) (by decide)
  have hb:=bit_cell h hr (c:=UpsV3.mB) (by decide)
  rcases ha with ha|ha <;> rcases hw with hw|hw <;> rcases hv with hv|hv <;>
    rcases hs with hs|hs <;> rcases hk with hk|hk <;> rcases hb with hb|hb <;>
    simp only [ha,hw,hv,hs,hk,hb,hq] at hrow hwalk ⊢ <;> simp_all +decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem row {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (h : TableLocal compactTable tr t pub) (hr : r<tr.height t)
    (rank : Nat→Nat) (b : Nat) (hb : b≠B_UPB) (sd : Bool) :
    rowTraffic compactInteractions (patchWindowCounters tr t rank) t r pub b sd=
      rowTraffic compactInteractions tr t r pub b sd := by
  by_cases hd : tr.cell t r UpsV3.rd=1
  · obtain ⟨hs,hk,hm⟩:=reader_walk_gates h hr hd
    have hne : B_UPB≠b := Ne.symm hb
    have hz : ¬ ((0:Fp)+0=1) := by decide
    simp only [UpsV3.rd,UpsV3.mS,UpsV3.mK,UpsV3.mB] at hd hs hk hm
    simp [rowTraffic,compactInteractions,UpsV3.interactions,send,recv,
      Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,
      patchWindowCounters,UpsV3.edgeMsg,UpsV3.bmapMsg,UpsV3.upbMsg,UpsV3.regs,UpsV3.reg,UpsV3.upsId,UpsV3.Lexpr,
      mid,smul,c,k,Trace.height,List.range_succ,UpsV3.vb,UpsV3.qb,UpsV3.sf,UpsV3.wt3,UpsV3.tau,UpsV3.rootRid,UpsV3.gD,UpsV3.dI,UpsV3.dL,UpsV3.pres,UpsV3.vid,UpsV3.L0,UpsV3.L1,UpsV3.L2,UpsV3.j,UpsV3.qpos,UpsV3.b,UpsV3.mS,UpsV3.mK,UpsV3.mB,UpsV3.u,UpsV3.nN,UpsV3.nI,UpsV3.nib,UpsV3.nN2,UpsV3.nI2,UpsV3.ek,UpsV3.wbm,UpsV3.hv,UpsV3.rd,UpsV3.sN,UpsV3.spos,UpsV3.rb,UpsV3.plen,UpsV3.pdep,UpsV3.rcid,UpsV3.gMs,UpsV3.gMr,UpsV3.idx,UpsV3.rx,UpsV3.qlen,UpsV3.jm,UpsV3.mBv,UpsV3.mCv,UpsV3.clen,hd,hs,hk,hm,hne,hz]
  · simp only [UpsV3.rd] at hd
    simp [rowTraffic,compactInteractions,UpsV3.interactions,send,recv,
      Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,
      patchWindowCounters,UpsV3.edgeMsg,UpsV3.bmapMsg,UpsV3.upbMsg,UpsV3.regs,UpsV3.reg,UpsV3.upsId,UpsV3.Lexpr,
      mid,smul,c,k,Trace.height,List.range_succ,UpsV3.vb,UpsV3.qb,UpsV3.sf,UpsV3.wt3,UpsV3.tau,UpsV3.rootRid,UpsV3.gD,UpsV3.dI,UpsV3.dL,UpsV3.pres,UpsV3.vid,UpsV3.L0,UpsV3.L1,UpsV3.L2,UpsV3.j,UpsV3.qpos,UpsV3.b,UpsV3.mS,UpsV3.mK,UpsV3.mB,UpsV3.u,UpsV3.nN,UpsV3.nI,UpsV3.nib,UpsV3.nN2,UpsV3.nI2,UpsV3.ek,UpsV3.wbm,UpsV3.hv,UpsV3.rd,UpsV3.sN,UpsV3.spos,UpsV3.rb,UpsV3.plen,UpsV3.pdep,UpsV3.rcid,UpsV3.gMs,UpsV3.gMr,UpsV3.idx,UpsV3.rx,UpsV3.qlen,UpsV3.jm,UpsV3.mBv,UpsV3.mCv,UpsV3.clen,hd]

 theorem count {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal compactTable tr t pub) (rank : Nat→Nat)
    (b : Nat) (hb : b≠B_UPB) (sd : Bool) (msg : List Fp) :
    tableBusCount compactTable.interactions (patchWindowCounters tr t rank) t pub b sd msg=
      tableBusCount compactTable.interactions tr t pub b sd msg := by
  rw [tableBusCount_eq,tableBusCount_eq]
  congr 1
  unfold List.flatMap
  congr 1
  apply List.map_congr_left
  intro r hr
  exact row h (List.mem_range.mp hr) rank b hb sd

end ZkFormal.NearV3.Candidates.WindowPatchOtherTraffic
