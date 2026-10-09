import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundIndex
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundRecordBound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec ProcPriorCodecSoundGeometry
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem next_index (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r : Nat}
    (hr:r+1<tr.height t) (hR:cv tr t r kR=1) (hnR:cv tr t (r+1) kR=1)
    (hb:cv tr t r kidx<cv tr t r NN) (hN:cv tr t r NN≤4096) :
    cv tr t (r+1) kidx<cv tr t r NN := by
  have hr0:r<tr.height t := by omega
  have kn:=kinds hL hr
  have kp:=kinds hL hr0
  have hnz:cv tr t (r+1) kZ=0 := by omega
  have be:=hL.bool hr0 (kind_member (Table.boolC e7) (by simp [cKind,boolCols]) (by decide +kernel))
  have br:=hL.bool hr0 (kind_member (Table.boolC rend) (by simp [cKind,boolCols]) (by decide +kernel))
  have bk:=hL.bool hr0 (kind_member (Table.boolC ekl) (by simp [cKind,boolCols]) (by decide +kernel))
  obtain ⟨qc,hc⟩:=Mem.zdvd hL hr0 (rec_member
    (mul3 (c kR) (notE (c e7)) (sub (n kidx) (c kidx))) (by simp [cRec]) (by decide +kernel))
  obtain ⟨qs,hs⟩:=Mem.zdvd hL hr0 (rec_member
    (mul3 (c e7) (c fS) (sub (n kidx) (c kidx))) (by simp [cRec]) (by decide +kernel))
  obtain ⟨qf,hf⟩:=Mem.zdvd hL hr0 (rec_member
    (mul3 (c e7) (c fR) (sub (n kidx) (c kidx))) (by simp [cRec]) (by decide +kernel))
  obtain ⟨qr,hrr⟩:=Mem.zdvd hL hr0 (rec_member
    (sub (c rend) (.mul (c fA) (c e7))) (by simp [cRec]) (by decide +kernel))
  obtain ⟨qe,he⟩:=Mem.zdvd hL hr0 (rec_member
    (mul3 (c rend) (c ekl) (notE (n kZ))) (by simp [cRec]) (by decide +kernel))
  obtain ⟨qi,hi⟩:=Mem.zdvd hL hr0 (rec_member
    (mul3 (c rend) (notE (c ekl)) (sub (n kidx) (.add (c kidx) (k 1)))) (by simp [cRec]) (by decide +kernel))
  have ln:=Codec.lt (tr:=tr) (t:=t) (r+1) kidx
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp be with hz|hz
  · zs hc [hR,hz,nx hr]; omega
  · by_cases hS:cv tr t r fS=1
    · zs hs [hz,hS,nx hr]; omega
    · by_cases hF:cv tr t r fR=1
      · zs hf [hz,hF,nx hr]; omega
      · have hA:cv tr t r fA=1 := by omega
        have hrd:cv tr t r rend=1 := by zs hrr [hA,hz];omega
        have hek:cv tr t r ekl=0 := by zs he [hrd,nx hr,hnz];omega
        have hne:cv tr t r kidx+1≠cv tr t r NN := by
          intro heq
          obtain ⟨q,hq⟩:=Mem.zdvd hL hr0 (kind_member
            (.mul (c kR) (sub (c ekl) (notE (.mul (sub (c kidx) (sub (c NN) (k 1))) (c ikl)))))
            (by simp [cKind,isZ]) (by decide +kernel))
          zs hq [hR,hek]
          simp only [Int.natCast_one,Int.natCast_zero] at hq
          have hz0:(cv tr t r kidx:Int)-((cv tr t r NN:Int)-1)=0 := by omega
          rw [hz0] at hq
          simp only [Int.zero_mul] at hq
          omega
        zs hi [hrd,hek,nx hr]
        omega

/-- The first-header square rule propagates to every active row. -/
theorem active_square (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r : Nat}
    (hr:r<tr.height t) (ha:cv tr t r act=1) (hn:cv tr t r nn≤64) :
    cv tr t r NN=cv tr t r nn*cv tr t r nn := by
  obtain ⟨f,hfr,hF,hc⟩:=ProcPriorCodecSoundOrigin.instance_origin hL r hr ha
  obtain ⟨q,hq⟩:=Mem.zdvd hL (show f<tr.height t by omega) (kind_member
    (.mul (c kF) (sub (c NN) (.mul (c nn) (c nn)))) (by simp [cKind]) (by decide +kernel))
  have hn0:=hc nn (by simp)
  have hN0:=hc NN (by simp)
  zs hq [hF,hn0,hN0]
  rw [←Int.natCast_mul] at hq
  have hp:=Nat.mul_le_mul hn hn
  have hlt:=Codec.lt (tr:=tr) (t:=t) r NN
  omega

/-- Record indices stay inside the authenticated grid, using only retained
corrected constraints and an active-row grid-size bound. -/
theorem record_bound (hL:ProcPriorCodecSoundRows.CLocal tr t pub)
    (hN:∀r,r<tr.height t→cv tr t r act=1→1≤cv tr t r NN ∧ cv tr t r NN≤4096) :
    ∀r,r<tr.height t→cv tr t r kR=1→cv tr t r kidx<cv tr t r NN := by
  intro r
  induction r with
  | zero=>
    intro hr hR
    have hk:=kinds hL hr
    have hf:=ProcPriorCodecSoundOrigin.first_flag hL hr (by omega)
    omega
  | succ r ih=>
    intro hr hR
    have kn:=kinds hL hr
    have ha:cv tr t (r+1) act=1 := by omega
    have hf:cv tr t (r+1) kF=0 := by omega
    have hc:=ProcPriorCodecSoundOrigin.constant_next hL NN (by simp) hr ha hf
    have hn:=hN (r+1) hr ha
    rcases ProcPriorCodecSoundIndex.predecessor hL hr hR with hh|⟨hp,_⟩
    · obtain ⟨q,hq⟩:=Mem.zdvd hL (show r<tr.height t by omega) (kind_member
        (.mul (c ehp) (n kidx)) (by simp [cKind]) (by decide +kernel))
      zs hq [hh.1,nx hr]
      have := Codec.lt (tr:=tr) (t:=t) (r+1) kidx
      omega
    · have hb:=ih (by omega) hp
      have hb':=next_index hL hr hp hR hb (by omega)
      omega
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundRecordBound
