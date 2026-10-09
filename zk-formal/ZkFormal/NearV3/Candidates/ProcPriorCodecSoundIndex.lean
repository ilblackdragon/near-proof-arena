import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundParameters
import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlIds
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundIndex
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec ProcPriorCodecSoundGeometry
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem addition_member (e : Expr) (he:e∈ProcPriorCodecActual.additions) :
    e∈ProcPriorCodecActual.constraints := by
  exact List.mem_append_right _ he

theorem trl_member (e : Expr) (he:e∈cTrl) : e∈ProcPriorCodecActual.constraints := by
  exact List.mem_append_left _ (List.mem_append_right _ he)

theorem rec_bool (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r x : Nat}
    (hr:r<tr.height t) (hR:cv tr t r kR=1) (hx:x∈recBoolCols) : cv tr t r x≤1 := by
  have hm:Expr.mul (c kR) (Table.boolC x)∈ProcPriorCodecActual.constraints :=
    kind_member (.mul (c kR) (Table.boolC x)) (by
      have hh:Expr.mul (c kR) (Table.boolC x)∈recBoolCols.map (fun x=>Expr.mul (c kR) (Table.boolC x)) := List.mem_map.mpr ⟨x,hx,rfl⟩
      simp only [cKind,List.mem_append]
      grind only) (by
      have hh:∀x∈recBoolCols,ProcPriorCodecActual.retiredKind.contains (.mul (c kR) (Table.boolC x))=false := by decide +kernel
      exact hh x hx)
  have hh:=hL r hr _ hm
  have hc:tr.cell t r kR=(1:Fp) := by
    have he:tr.cell t r kR=Fp.ofNat (cv tr t r kR) := (Fp.ofNat_toNat _).symm
    change tr.cell t r kR=Fp.ofNat 1
    simpa only [hR] using he
  change tr.cell t r kR*(Table.boolC x).eval tr t r pub=0 at hh
  rw [hc] at hh
  exact bool_of_eval (pub:=pub) (by grind only)

theorem predecessor (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r : Nat}
    (hr:r+1<tr.height t) (hR:cv tr t (r+1) kR=1) :
    (cv tr t r ehp=1 ∧ cv tr t (r+1) srcC=0) ∨
    (cv tr t r kR=1 ∧ cv tr t (r+1) srcC≤cv tr t r srcC+1) := by
  have hr0:r<tr.height t := by omega
  have kn:=kinds hL hr
  have kp:=kinds hL hr0
  have ha:cv tr t (r+1) act=1 := by omega
  have hp:=ProcPriorCodecSoundOrigin.active_prev hL hr ha
  have nh:cv tr t (r+1) kH=0 := by omega
  have nz:cv tr t (r+1) kZ=0 := by omega
  have na:cv tr t (r+1) kA=0 := by omega
  have nf:cv tr t (r+1) kF=0 := by omega
  have be:=hL.bool hr0 (kind_member (Table.boolC ehp) (by simp [cKind,boolCols]) (by decide +kernel))
  have bs:=hL.bool hr0 (kind_member (Table.boolC esj) (by simp [cKind,boolCols]) (by decide +kernel))
  obtain ⟨qh,hh⟩:=Mem.zdvd hL hr0 (kind_member
    (mul3 (c kH) (notE (c ehp)) (notE (n kH))) (by simp [cKind]) (by decide +kernel))
  obtain ⟨qz,hz⟩:=Mem.zdvd hL hr0 (trl_member
    (mul3 (c kZ) (notE (c esj)) (notE (n kZ))) (by simp [cTrl]))
  obtain ⟨qza,hza⟩:=Mem.zdvd hL hr0 (trl_member
    (mul3 (c kZ) (c esj) (notE (n kA))) (by simp [cTrl]))
  obtain ⟨qa,haa⟩:=Mem.zdvd hL hr0 (trl_member
    (mul3 (c kA) (notE (c esj)) (notE (n kA))) (by simp [cTrl]))
  obtain ⟨qaf,haf⟩:=Mem.zdvd hL hr0 (kind_member
    (mul3 (c kA) (c esj) (.mul (n act) (notE (n kF)))) (by simp [cKind]) (by decide +kernel))
  zs hh [nx hr,nh];zs hz [nx hr,nz];zs hza [nx hr,na];zs haa [nx hr,na];zs haf [nx hr,ha,nf]
  have hshape:cv tr t r kH=1 ∨ cv tr t r kR=1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp bs with hs|hs
    all_goals rw [hs] at hz hza haa haf; simp only [Int.natCast_zero,Int.natCast_one] at hz hza haa haf
    all_goals omega
  rcases hshape with hH|hRR
  · have he:cv tr t r ehp=1 := by rw [hH] at hh; simp only [Int.natCast_one] at hh; omega
    obtain ⟨q,hq⟩:=Mem.zdvd hL hr0 (addition_member (.mul (c ehp) (n srcC)) (by simp [ProcPriorCodecActual.additions]))
    zs hq [he,nx hr]
    have := Codec.lt (tr:=tr) (t:=t) (r+1) srcC
    exact Or.inl ⟨he,by omega⟩
  · refine Or.inr ⟨hRR,?_⟩
    have br:=hL.bool hr0 (kind_member (Table.boolC rend) (by simp [cKind,boolCols]) (by decide +kernel))
    have bk:=hL.bool hr0 (kind_member (Table.boolC ekl) (by simp [cKind,boolCols]) (by decide +kernel))
    have bc:=rec_bool hL hr0 hRR (x:=hasC) (by simp [recBoolCols])
    obtain ⟨qc,hc⟩:=Mem.zdvd hL hr0 (rec_member
      (.mul (sub (c kR) (c rend)) (sub (n srcC) (c srcC))) (by simp [cRec]) (by decide +kernel))
    obtain ⟨qe,he⟩:=Mem.zdvd hL hr0 (rec_member
      (mul3 (c rend) (c ekl) (notE (n kZ))) (by simp [cRec]) (by decide +kernel))
    obtain ⟨qi,hi⟩:=Mem.zdvd hL hr0 (addition_member
      (mul3 (c rend) (notE (c ekl)) (sub (n srcC) (.add (c srcC) (c hasC)))) (by simp [ProcPriorCodecActual.additions]))
    have l0:=Codec.lt (tr:=tr) (t:=t) r srcC
    have l1:=Codec.lt (tr:=tr) (t:=t) (r+1) srcC
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp br with hrend|hrend
    · zs hc [hRR,hrend,nx hr];omega
    · have hek:cv tr t r ekl=0 := by zs he [hrend,nx hr,nz];omega
      zs hi [hrend,hek,nx hr]
      omega

theorem source_le_row (hL:ProcPriorCodecSoundRows.CLocal tr t pub) :
    ∀r,r<tr.height t→cv tr t r kR=1→cv tr t r srcC≤r := by
  intro r
  induction r with
  | zero=>
    intro hr hR
    have hk:=kinds hL hr
    have hf:=ProcPriorCodecSoundOrigin.first_flag hL hr (by omega)
    omega
  | succ r ih=>
    intro hr hR
    rcases predecessor hL hr hR with hh|⟨hp,hb⟩
    · omega
    · have := ih (by omega) hp;omega

theorem live_index (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r : Nat}
    (hr:r<tr.height t) (hh:tr.height t≤2^22) (hn:cv tr t r nn≤64)
    (hm:(Expr.mul (c rs) (c nzb)).eval tr t r pub=1) :
    cv tr t r useC=0 ∧ cv tr t r kidx=cv tr t r srcC*cv tr t r nn := by
  have hs:=public_id_start hL hr hm
  have hS:=(start hL hr hs).1
  have hR:=(sender_kind hL hr hS).1
  have hz:cv tr t r nzb=1 := by
    have hcell:tr.cell t r rs=(1:Fp) := by
      change tr.cell t r rs=Fp.ofNat 1
      rw [←hs];exact (Fp.ofNat_toNat _).symm
    change tr.cell t r rs*tr.cell t r nzb=1 at hm
    rw [hcell] at hm
    have he:tr.cell t r nzb=(1:Fp) := by grind only
    have ht:=congrArg Fp.toNat he
    exact ht
  obtain ⟨qu,hu⟩:=Mem.zdvd hL hr (addition_member
    (.mul (c rs) (.mul (c useC) (c nzb))) (by simp [ProcPriorCodecActual.additions,isZ]))
  zs hu [hs,hz]
  have lu:=Codec.lt (tr:=tr) (t:=t) r useC
  have hu0:cv tr t r useC=0 := by omega
  refine ⟨hu0,?_⟩
  have hsbound:=source_le_row hL r hr hR
  have hprod:cv tr t r srcC*cv tr t r nn<2013265921 := by
    have hp:=Nat.mul_le_mul (show cv tr t r srcC≤2^22 by omega) hn
    omega
  obtain ⟨qi,hi⟩:=Mem.zdvd hL hr (addition_member
    (.mul (c rs) (sub (c kidx) (.add (.mul (c srcC) (c nn)) (c useC))))
    (by simp [ProcPriorCodecActual.additions]))
  zs hi [hs,hu0]
  rw [←Int.natCast_mul] at hi
  have hk:=Codec.lt (tr:=tr) (t:=t) r kidx
  omega
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundIndex
