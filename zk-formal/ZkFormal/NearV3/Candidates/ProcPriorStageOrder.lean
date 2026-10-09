import ZkFormal.NearV3.Candidates.ProcPriorRawBackward
namespace ZkFormal.NearV3.Candidates.ProcPriorStageOrder
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorVertical4Linear
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def rank (tr:Trace Fp) (t r:Nat):Nat:=cv tr t r (stage 1)+2*cv tr t r (stage 2)+3*cv tr t r (stage 3)

theorem bit (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (j:Nat) (hj:j<4) :cv tr t r (stage j)≤1 := by
  have cases:j=0∨j=1∨j=2∨j=3:=by omega
  rcases cases with rfl|rfl|rfl|rfl <;>
    exact hL.bool hr (ProcPriorVerticalMemorySound.window_member (Table.boolC _) (by simp [windows]))

theorem stay (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hl:cv tr t r last=0) (j:Nat) (hj:j<4) :
    cv tr t (r+1) (stage j)=cv tr t r (stage j) := by
  have hr0:r<tr.height t:=by omega
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr0 (ProcPriorVerticalMemorySound.window_member
    (.mul (.mul .isTransition (sub (k 1) (c last))) (sub (n (stage j)) (c (stage j))))
    (List.mem_append_right _ (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩)))
  zs hq [Codec.nx hr,hl]
  simp only [zev,Mem.tenv_last_zero hr] at hq
  have h0:=bit hL hr0 j hj
  have h1:=bit hL hr j hj
  omega

theorem advance (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hl:cv tr t r last=1) (j:Nat) (hj:j<3) :
    cv tr t (r+1) (stage (j+1))=cv tr t r (stage j) := by
  have hr0:r<tr.height t:=by omega
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr0 (ProcPriorVerticalMemorySound.window_member
    (.mul (.mul .isTransition (c last)) (sub (n (stage (j+1))) (c (stage j)))) (by
      have cases:j=0∨j=1∨j=2:=by omega
      rcases cases with rfl|rfl|rfl <;> simp [windows]))
  zs hq [Codec.nx hr,hl]
  simp only [zev,Mem.tenv_last_zero hr] at hq
  have h0:=bit hL hr0 j (by omega)
  have h1:=bit hL hr (j+1) (by omega)
  omega

theorem last_no_three (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hl:cv tr t r last=1) :cv tr t r (stage 3)=0 := by
  have hr0:r<tr.height t:=by omega
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr0 (ProcPriorVerticalMemorySound.window_member
    (.mul (.mul .isTransition (c last)) (c (stage 3))) (by simp [windows]))
  zs hq [Codec.nx hr,hl]
  simp only [zev,Mem.tenv_last_zero hr] at hq
  have h0:=bit hL hr0 3 (by decide)
  omega

theorem rank_step (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) :rank tr t r≤rank tr t (r+1) := by
  have hb:=hL.bool (show r<tr.height t by omega) (ProcPriorVerticalMemorySound.window_member
    (Table.boolC last) (by simp [windows]))
  by_cases hl:cv tr t r last=0
  · have h1:=stay hL hr hl 1 (by decide)
    have h2:=stay hL hr hl 2 (by decide)
    have h3:=stay hL hr hl 3 (by decide)
    unfold rank;omega
  · have hl1:cv tr t r last=1:=by omega
    have h1:=advance hL hr hl1 0 (by decide)
    have h2:=advance hL hr hl1 1 (by decide)
    have h3:=advance hL hr hl1 2 (by decide)
    simp only [Nat.reduceAdd] at h1 h2 h3
    have hz:=last_no_three hL hr hl1
    unfold rank;omega

theorem monotone (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    {a b:Nat} (ha:a≤b) (hb:b<tr.height t) :rank tr t a≤rank tr t b := by
  induction b with
  | zero=>have he:a=0:=(by omega);subst a;exact Nat.le_refl _
  | succ b ih=>
    by_cases he:a=b+1
    · subst a;exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega) (by omega)) (rank_step hL hb)

theorem partition (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) :cv tr t r (stage 0)+cv tr t r (stage 1)+cv tr t r (stage 2)+cv tr t r (stage 3)=1 := by
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (ProcPriorVerticalMemorySound.window_member
    (sub (.add (c (stage 0)) (.add (c (stage 1)) (.add (c (stage 2)) (c (stage 3))))) (k 1)) (by simp [windows]))
  zs hq []
  have h0:=bit hL hr 0 (by decide)
  have h1:=bit hL hr 1 (by decide)
  have h2:=bit hL hr 2 (by decide)
  have h3:=bit hL hr 3 (by decide)
  omega

theorem raw_rank (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) :cv tr t r (stage 2)=1 ↔ rank tr t r=2 := by
  have hp:=partition hL hr
  unfold rank
  omega

theorem raw_interval (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    {a b q:Nat} (ha:a≤q) (hq:q≤b) (hb:b<tr.height t)
    (hsa:cv tr t a (stage 2)=1) (hsb:cv tr t b (stage 2)=1) :cv tr t q (stage 2)=1 := by
  have hqa:=monotone hL ha (by omega)
  have hqb:=monotone hL hq hb
  rw [(raw_rank hL (by omega)).mp hsa] at hqa
  rw [(raw_rank hL hb).mp hsb] at hqb
  exact (raw_rank hL (by omega)).mpr (by omega)
end ZkFormal.NearV3.Candidates.ProcPriorStageOrder
