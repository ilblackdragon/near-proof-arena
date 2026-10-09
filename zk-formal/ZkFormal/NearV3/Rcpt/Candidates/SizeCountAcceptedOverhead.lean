import ZkFormal.NearV3.Rcpt.Candidates.SizeCountNativeOverhead
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountPreparedK
import ZkFormal.NearV3.Rcpt.Candidates.DictionaryCount
import ZkFormal.NearV3.Assembly.PreparedSources
import ZkFormal.NearV3.Assembly.NativeWitnessFields
import ZkFormal.NearV3.Assembly.NativeMain

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Near NearSpec NearSpecV3 Assembly

private theorem distinct_count (es : List ProofEntry) : (distinctKeys es).length≤es.length := by
  induction es with
  | nil => simp [distinctKeys]
  | cons e es ih =>
    unfold distinctKeys
    dsimp only
    split <;> simp only [List.length_cons] <;> omega

/-- The actual unchanged native checker implies the fixed public overhead cap.
No distinct-source-key restriction is used: the native dictionary cardinality
guard and arbitrary filler entries are preserved. -/
theorem accepted_fixed_overhead {cb wb : Bytes} {hint : Hint} {p : Prep}
    {k : WalkD0} {w : StateWitness}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k)
    (hw : decodeW wb=.ok w) (hc : checkD0 cb wb=.ok ()) :
    fixedOverhead p k.c.chunkInner≤8388608 := by
  obtain ⟨raw,codes,_,hd,hraw,_,hinner,_⟩ := checkD0_witness_fields hk hw hc
  have hshape := decodeStateWitness_shape hd hraw
  have hencoded := decodeStateWitness_encodeSW_size hd
  have hdict := checkD0_dictionary_count hk hw hc
  have hprepared := preparedSourceLists_length k.sourceBlks (prepD0_source_lists hp hk)
  have hcount : p.lists.length≤w.entries.length := by
    rw [hprepared,←hdict]
    exact distinct_count w.entries
  have hfixed := shape_fixed_overhead w p.lists.length hshape hcount (by omega)
  obtain ⟨_,_,_,_,himplicit,_⟩ := checkD0_native_steps hk hw hc
  have hK := prepD0_implicit_count hp hk
  unfold fixedOverhead
  rw [hinner,himplicit,←hK] at hfixed
  exact hfixed

/-- Candidate public construction accepts every unchanged accepted native input. -/
theorem accepted_counted_prepared {cb wb : Bytes} {hint : Hint} {p : Prep}
    {k : WalkD0} {w : StateWitness}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k)
    (hw : decodeW wb=.ok w) (hc : checkD0 cb wb=.ok ()) :
    countedPreparedBytes p k.c.chunkInner=
      some (Public.preparedBytes p (fixedOverhead p k.c.chunkInner)) := by
  have ho := accepted_fixed_overhead hp hk hw hc
  simp [countedPreparedBytes,ho]

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
