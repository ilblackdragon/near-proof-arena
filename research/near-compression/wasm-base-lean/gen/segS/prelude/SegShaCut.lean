namespace SegSha

theorem cutT_segT {nloc ngl : Nat} {t : Nat} {cs : List String} {base : Nat}
    (hT : (t = 30 ∧ cs = Cut.In.cols ∧ base = pubCtxIn) ∨ (t = 31 ∧ cs = Cut.Out.cols ∧ base = pubCtxOut)) :
    SegT t := ⟨by rcases hT with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> decide⟩

end SegSha
