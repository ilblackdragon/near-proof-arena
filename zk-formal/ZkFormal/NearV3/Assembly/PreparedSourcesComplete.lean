import ZkFormal.NearV3.Assembly.SourceShuffle
import ZkFormal.NearV3.Rcpt.Link.CheckedSources
import ZkFormal.NearV3.Rcpt.Candidates.PreparedReceipts

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched Rcpt.Candidates

theorem sourceDescriptors_shuffle {entries : List ProofEntry} {own : Nat} {b : Blk}
    (hv : ∀ x ∈ b.slots, SourceSlotValid entries own b x)
    (hs : ∃ shuffled, shuffleWithSeed (selectedEntries entries b b.slots) b.hdr.prevHash = some shuffled) :
    ∃ shuffled, shuffleWithSeed (slotDescriptors b b.slots) b.hdr.prevHash = some shuffled := by
  obtain ⟨selected,hs⟩ := hs
  have hm := shuffleWithSeed_map (sourceEntry entries) (slotDescriptors b b.slots) b.hdr.prevHash
  rw [slotDescriptors_selected entries own b b.slots hv] at hm
  have he : selectedProofs entries b b.slots = selectedEntries entries b b.slots := by
    unfold selectedProofs selectedEntries
    congr 1
  rw [he,hs] at hm
  cases ho : shuffleWithSeed (slotDescriptors b b.slots) b.hdr.prevHash with
  | none => simp [ho] at hm
  | some out => exact ⟨out,rfl⟩

private theorem forIn_yield_exists {α β : Type} (f : α → β → Except String (ForInStep β)) :
    ∀ (xs : List α), (∀ x ∈ xs, ∀ acc, ∃ next, f x acc = .ok (.yield next)) →
      ∀ acc, ∃ out, forIn xs acc f = .ok out
  | [], _, acc => ⟨acc,rfl⟩
  | x :: xs, hf, acc => by
    obtain ⟨next,hn⟩ := hf x (by simp) acc
    obtain ⟨out,ho⟩ := forIn_yield_exists f xs (fun y hy => hf y (List.mem_cons_of_mem _ hy)) next
    refine ⟨out,?_⟩
    rw [List.forIn_cons,hn]
    exact ho

theorem preparedSourceLists_exists {entries : List ProofEntry} {own : Nat} {blocks : List Blk}
    (hv : ∀ b ∈ blocks, ∀ x ∈ b.slots, SourceSlotValid entries own b x)
    (hs : ∀ b ∈ blocks, ∃ shuffled,
      shuffleWithSeed (selectedEntries entries b b.slots) b.hdr.prevHash = some shuffled) :
    ∃ lists, preparedSourceLists blocks = .ok lists := by
  unfold preparedSourceLists
  apply forIn_yield_exists
  intro b hb acc
  obtain ⟨shuffled,hsh⟩ := sourceDescriptors_shuffle (hv b hb) (hs b hb)
  refine ⟨acc ++ shuffled,?_⟩
  simp only [slotSources_eq,hsh,pure,Except.pure,bind,Except.bind]

theorem checkD0_prepared_sources {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0 cb wb = .ok ()) :
    ∃ lists, preparedSourceLists k.sourceBlks = .ok lists :=
  preparedSourceLists_exists (checkD0_sources_verified hk hw h) (checkD0_sources_shuffle hk hw h)

end ZkFormal.NearV3.Assembly
