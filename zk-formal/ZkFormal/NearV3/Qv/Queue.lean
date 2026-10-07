import NearSpecV3.RuntimeD0
import ZkFormal.Near.Spec.SoundAccount

/-! Exact queue-value semantics for the missing qv parser. Equality of u64
indices is equivalent to eight byte equalities; absent queues are accepted. -/
namespace ZkFormal.NearV3.Qv
open NearSpec NearSpecV3

theorem leNat_injective {a b : Bytes} (hlen : a.length = b.length) (he : leNat a = leNat b) : a = b := by
  calc
    a = leN a.length (leNat a) := (ZkFormal.Near.Sound.leN_leNat a).symm
    _ = leN b.length (leNat b) := by rw [hlen,he]
    _ = b := ZkFormal.Near.Sound.leN_leNat b

def EmptyQueue : Option Bytes → Prop
  | none => True
  | some b => b.length = 16 ∧ b.take 8 = b.drop 8

theorem queueEmpty_iff (v : Option Bytes) (what : String) :
    queueEmpty v what = .ok () ↔ EmptyQueue v := by
  cases v with
  | none => simp [queueEmpty,EmptyQueue]
  | some b =>
    by_cases hl : b.length = 16
    · simp only [queueEmpty,hl,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,EmptyQueue,true_and]
      by_cases he : leNat (b.take 8) = leNat (b.drop 8)
      · have hbytes : b.take 8 = b.drop 8 := leNat_injective (by simp [hl]) he
        simp [he,hbytes]
      · have hbytes : b.take 8 ≠ b.drop 8 := fun h => he (congrArg leNat h)
        simp [he,hbytes]
    · simp [queueEmpty,EmptyQueue,hl]

theorem emptyQueue_some_iff (b : Bytes) :
    EmptyQueue (some b) ↔ ∃ index : Bytes, index.length = 8 ∧ b = index ++ index := by
  constructor
  · rintro ⟨hl,he⟩
    refine ⟨b.take 8,by simp [hl],?_⟩
    rw [he]
    calc
      b = b.take 8 ++ b.drop 8 := (List.take_append_drop 8 b).symm
      _ = b.drop 8 ++ b.drop 8 := congrArg (fun t => t ++ b.drop 8) he
  · rintro ⟨index,hl,rfl⟩
    constructor
    · simp [hl]
    · rw [show 8 = index.length by omega,List.take_left,List.drop_left]

theorem emptyQueue_bytewise (b : Bytes) (hl : b.length = 16) :
    EmptyQueue (some b) ↔ ∀ i, i < 8 → b.getD i 0 = b.getD (8+i) 0 := by
  constructor
  · intro h i hi
    have he := congrArg (fun l : Bytes => l.getD i 0) h.2
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_take,hi,↓reduceIte,List.getElem?_drop] using he
  · intro h
    refine ⟨hl,?_⟩
    apply List.ext_getElem (by simp [hl])
    intro i hi hi'
    have hi8 : i < 8 := by simpa [hl] using hi
    have he := h i hi8
    rw [← List.getElem_eq_getD (h := (show i < b.length by omega)) 0,
      ← List.getElem_eq_getD (h := (show 8+i < b.length by omega)) 0] at he
    simpa only [List.getElem_take,List.getElem_drop] using he

end ZkFormal.NearV3.Qv
