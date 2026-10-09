import ZkFormal.NearV3.Candidates.ProcPriorCodecGridRecords
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecGridHeader
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec
open ProcPriorCodecSoundGeometry
variable {tr:Trace Fp} {t:Nat} {pub:List Fp}
set_option maxHeartbeats 1000000

theorem first (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r:Nat}
    (hr:r<tr.height t) (hf:cv tr t r kF=1) : cv tr t r kH=1 ∧ cv tr t r pos=0 := by
  have K:=kinds hL hr
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (kind_member (.mul (c kF) (c pos)) (by simp [cKind]) (by decide +kernel))
  zs hq [hf]
  have :=Codec.lt (tr:=tr) (t:=t) r pos
  exact ⟨by omega,by omega⟩

theorem end_flag (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r:Nat}
    (hr:r<tr.height t) (hh:cv tr t r kH=1) (hp:cv tr t r pos=4) :cv tr t r ehp=1 := by
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (kind_member
    (.mul (c kH) (sub (c ehp) (notE (.mul (sub (c pos) (k 4)) (c ihp)))))
    (by simp [cKind,isZ]) (by decide +kernel))
  zs hq [hh,hp]
  have :=Codec.lt (tr:=tr) (t:=t) r ehp
  omega

theorem step (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r j:Nat}
    (hr:r<tr.height t) (hh:cv tr t r kH=1) (hp:cv tr t r pos=j) (hj:j<4) :
    r+1<tr.height t ∧ cv tr t (r+1) kH=1 ∧ cv tr t (r+1) pos=j+1 := by
  have K:=kinds hL hr
  have hr1:=act_next hL hr (by omega)
  have hb:=hL.bool hr (kind_member (Table.boolC ehp) (by simp [cKind,boolCols]) (by decide +kernel))
  obtain ⟨q0,h0⟩:=Mem.zdvd hL hr (kind_member
    (.mul (c kH) (.mul (sub (c pos) (k 4)) (c ehp)))
    (by simp [cKind,isZ]) (by decide +kernel))
  have he:cv tr t r ehp=0:=by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h|h
    · exact h
    · zs h0 [hh,hp,h];omega
  obtain ⟨q1,h1⟩:=Mem.zdvd hL hr (kind_member
    (mul3 (c kH) (notE (c ehp)) (notE (n kH))) (by simp [cKind]) (by decide +kernel))
  obtain ⟨q2,h2⟩:=Mem.zdvd hL hr (kind_member
    (.mul encG (sub (n pos) (.add (c pos) (k 1)))) (by simp [cKind]) (by decide +kernel))
  have hR:cv tr t r kR=0:=by omega
  have hZ:cv tr t r kZ=0:=by omega
  zs h1 [nx hr1,hh,he];zs h2 [nx hr1,hh,hR,hZ,hp]
  have :=Codec.lt (tr:=tr) (t:=t) (r+1) kH
  have :=Codec.lt (tr:=tr) (t:=t) (r+1) pos
  exact ⟨hr1,by omega,by omega⟩

theorem header (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {f:Nat}
    (hf:f<tr.height t) (hF:cv tr t f kF=1) :
    ∀j,j<5→f+j<tr.height t ∧ cv tr t (f+j) kH=1 ∧ cv tr t (f+j) pos=j := by
  intro j
  induction j with
  | zero => intro _; simpa using And.intro hf (first hL hf hF)
  | succ j ih =>
    intro hj
    obtain ⟨hb,hh,hp⟩:=ih (by omega)
    simpa [Nat.add_assoc] using step hL hb hh hp (by omega)

theorem first_record (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {f:Nat}
    (hf:f<tr.height t) (hF:cv tr t f kF=1) :
    f+5<tr.height t ∧ cv tr t (f+5) rs=1 ∧ cv tr t (f+5) kidx=0 := by
  obtain ⟨hb,hh,hp⟩:=header hL hf hF 4 (by decide)
  have he:=end_flag hL hb hh hp
  have K:=kinds hL hb
  have hr1:=act_next hL hb (by omega)
  obtain ⟨q1,h1⟩:=Mem.zdvd hL hb (kind_member
    (.mul (c ehp) (notE (n rs))) (by simp [cKind]) (by decide +kernel))
  obtain ⟨q2,h2⟩:=Mem.zdvd hL hb (kind_member
    (.mul (c ehp) (n kidx)) (by simp [cKind]) (by decide +kernel))
  zs h1 [nx hr1,he];zs h2 [nx hr1,he]
  have :=Codec.lt (tr:=tr) (t:=t) (f+4+1) rs
  have :=Codec.lt (tr:=tr) (t:=t) (f+4+1) kidx
  have eq:f+4+1=f+5:=by omega
  rw [eq] at *
  exact ⟨hr1,by omega,by omega⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecGridHeader
