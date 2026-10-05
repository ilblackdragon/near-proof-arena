import ZkFormal.Near.Render.Proof.Base

/-!
# ZkFormal.Near.Render.Proof.ShaFit1 — node serializations of `mkInfo` are short bytes

`mkInfo` fills `pre`/`post` (and the digests `dpre`/`dpost`) in a loop over
the post-order; every entry ever written is `toNats (ser vh dig nr)` with a
32-byte value hash and windows of at most 32 bytes, so (`pre_ok`, `post_ok`)
every `pre n` / `post n` has bytes `< 256` and at most `sz0 (nodeAt n)` of
them, `sz0 nr` the serialized size with all windows 32 bytes (the `nodeSize`
of `Spec/Trie.lean` without the touched value).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

/-- Serialized size of a record, all windows 32 bytes. -/
def sz0 (nr : NodeRec) : Nat := (ser (zeros 32) (fun _ => zeros 32) nr).length

theorem zeros_len : ∀ n, (zeros n).length = n
  | 0 => rfl
  | n + 1 => by simp [zeros, zeros_len n]

theorem concatAll_len (l : List Bytes) : (concatAll l).length = (l.map List.length).sum := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp [concatAll, ih]

theorem kids_len_le (dig : Nat → Bytes) (hd : ∀ c, (dig c).length ≤ 32) :
    ∀ kids : List Kid, ((kids.map (kidBytes dig)).map List.length).sum ≤
      ((kids.map (kidBytes fun _ => zeros 32)).map List.length).sum
  | [] => Nat.le_refl _
  | k :: ks => by
    have ih := kids_len_le dig hd ks
    simp only [List.map_cons, List.sum_cons]
    cases k with
    | none => simp only [kidBytes]; omega
    | hash h => simp only [kidBytes]; omega
    | node c => simp only [kidBytes, zeros_len]; have := hd c; omega

theorem vref_len_le (vh : Bytes) (hv : vh.length ≤ 32) (v : VSlot) :
    (vrefBytes vh v).length ≤ (vrefBytes (zeros 32) v).length := by
  cases v <;> simp [vrefBytes, zeros_len] <;> omega

theorem ser_len_le (vh : Bytes) (dig : Nat → Bytes) (hv : vh.length ≤ 32)
    (hd : ∀ c, (dig c).length ≤ 32) (nr : NodeRec) : (ser vh dig nr).length ≤ sz0 nr := by
  have hk := kids_len_le dig hd
  unfold sz0
  cases nr with
  | leaf k v mem =>
    have := vref_len_le vh hv v
    simp only [ser, List.length_append]; omega
  | ext k kid mem =>
    have := hk [kid]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
    simp only [ser, List.length_append]; omega
  | branch v kids mem =>
    have := hk kids
    cases v with
    | none => simp only [ser, List.length_append, concatAll_len]; omega
    | some s =>
      have := vref_len_le vh hv s
      simp only [ser, List.length_append, concatAll_len]; omega

theorem toNats_lt (b : Bytes) : ∀ x ∈ toNats b, x < 256 := by
  intro x hx
  simp only [toNats, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact y.toNat_lt

/-! ## The loop of `mkInfo` -/

abbrev LS := Array (List Nat) × Array (List Nat) × Array Bytes × Array Bytes

/-- One step of `mkInfo`'s serialization loop. -/
def loopF (ns : Array NodeRec) (vpre vpost : Array (List Nat)) (s : LS) (n : Nat) : LS :=
  (s.1.set! n (toNats (ser (sha256 (ofNats (vpre.getD n []))) (fun c => s.2.2.1.getD c [])
      (ns.getD n (.branch none [] 0)))),
   s.2.1.set! n (toNats (ser (sha256 (ofNats (vpost.getD n []))) (fun c => s.2.2.2.getD c [])
      (ns.getD n (.branch none [] 0)))),
   s.2.2.1.set! n (sha256 (ser (sha256 (ofNats (vpre.getD n []))) (fun c => s.2.2.1.getD c [])
      (ns.getD n (.branch none [] 0)))),
   s.2.2.2.set! n (sha256 (ser (sha256 (ofNats (vpost.getD n []))) (fun c => s.2.2.2.getD c [])
      (ns.getD n (.branch none [] 0)))))

/-- The loop state's invariant. -/
def SerOk (ns : Array NodeRec) (a : Array (List Nat)) : Prop :=
  ∀ n, (a.getD n []).length ≤ sz0 (ns.getD n (.branch none [] 0)) ∧ ∀ x ∈ a.getD n [], x < 256

def DigOk (a : Array Bytes) : Prop := ∀ c, (a.getD c []).length ≤ 32

structure LoopInv (ns : Array NodeRec) (s : LS) : Prop where
  pre : SerOk ns s.1
  post : SerOk ns s.2.1
  dpre : DigOk s.2.2.1
  dpost : DigOk s.2.2.2

theorem getD_set! {α : Type} (a : Array α) (i : Nat) (v : α) (n : Nat) (d : α) :
    (a.set! i v).getD n d = if i = n ∧ i < a.size then v else a.getD n d := by
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h1 : i = n
  · subst h1
    by_cases h2 : i < a.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem serOk_set {ns : Array NodeRec} {a : Array (List Nat)} (h : SerOk ns a) (i : Nat) (vh : Bytes)
    (dig : Nat → Bytes) (hv : vh.length ≤ 32) (hd : ∀ c, (dig c).length ≤ 32) :
    SerOk ns (a.set! i (toNats (ser vh dig (ns.getD i (.branch none [] 0))))) := by
  intro n
  rw [getD_set!]
  split
  · rename_i hi
    rw [← hi.1]
    refine ⟨?_, toNats_lt _⟩
    simp only [toNats, List.length_map]
    exact ser_len_le vh dig hv hd _
  · exact h n

theorem digOk_set {a : Array Bytes} (h : DigOk a) (i : Nat) (b : Bytes) :
    DigOk (a.set! i (sha256 b)) := by
  intro c
  rw [getD_set!]
  split
  · simp [ArenaCore.sha256_length]
  · exact h c

theorem loopInv_step (ns : Array NodeRec) (vpre vpost : Array (List Nat)) (s : LS) (n : Nat)
    (h : LoopInv ns s) : LoopInv ns (loopF ns vpre vpost s n) :=
  ⟨serOk_set h.pre n _ _ (by simp [ArenaCore.sha256_length]) h.dpre,
   serOk_set h.post n _ _ (by simp [ArenaCore.sha256_length]) h.dpost,
   digOk_set h.dpre n _, digOk_set h.dpost n _⟩

theorem loopInv_foldl (ns : Array NodeRec) (vpre vpost : Array (List Nat)) :
    ∀ (l : List Nat) (s : LS), LoopInv ns s → LoopInv ns (l.foldl (loopF ns vpre vpost) s)
  | [], _, h => h
  | n :: l, s, h => loopInv_foldl ns vpre vpost l _ (loopInv_step ns vpre vpost s n h)

theorem getD_replicate_nil {α : Type} (N n : Nat) : (Array.replicate N ([] : List α)).getD n [] = [] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem loopInv_init (ns : Array NodeRec) (N : Nat) :
    LoopInv ns (Array.replicate N [], Array.replicate N [], Array.replicate N [], Array.replicate N []) :=
  ⟨fun n => by rw [getD_replicate_nil]; simp, fun n => by rw [getD_replicate_nil]; simp,
   fun c => by rw [getD_replicate_nil]; simp, fun c => by rw [getD_replicate_nil]; simp⟩

section
variable (c : Claim) (e : Ext)

/-- The serialization loop of `mkInfo`, as a fold. -/
def loopOf : LS :=
  let ns := e.ns.toArray
  let N := ns.size
  let vpre : Array (List Nat) := (Array.range N).map fun k =>
    if (ns.getD k (.branch none [] 0)).touched then toNats (e.vals0 k) else []
  let vpost : Array (List Nat) := (Array.range N).map fun k =>
    if (ns.getD k (.branch none [] 0)).touched then toNats (e.valsAt e.rs.length k) else []
  (postOrder ns (N + 1) 0).foldl (loopF ns vpre vpost)
    (Array.replicate N [], Array.replicate N [], Array.replicate N [], Array.replicate N [])

theorem mkInfo_pre : (mkInfo c e).pre = (loopOf e).1 := by
  simp only [mkInfo, List.forIn_pure_yield_eq_foldl, Id.run, pure_bind, bind_pure_comp]
  rfl

theorem mkInfo_post : (mkInfo c e).post = (loopOf e).2.1 := by
  simp only [mkInfo, List.forIn_pure_yield_eq_foldl, Id.run, pure_bind, bind_pure_comp]
  rfl

theorem loopOf_inv : LoopInv e.ns.toArray (loopOf e) :=
  loopInv_foldl _ _ _ _ _ (loopInv_init _ _)

theorem mkInfo_ns : (mkInfo c e).ns = e.ns.toArray := rfl

/-- **`pre n`**: bytes, at most `sz0 (nodeAt n)` of them.  (Interface used by
`ShaFit2/3`; `Good` is not needed for the loop form of `mkInfo`, but gives the
hash widths a closed form via `treeOf` would need.) -/
theorem pre_ok (_ : Good c e) (n : Nat) :
    ((mkInfo c e).pre.getD n []).length ≤ sz0 ((mkInfo c e).nodeAt n) ∧
      ∀ x ∈ (mkInfo c e).pre.getD n [], x < 256 := by
  rw [mkInfo_pre]; exact (loopOf_inv e).pre n

theorem post_ok (_ : Good c e) (n : Nat) :
    ((mkInfo c e).post.getD n []).length ≤ sz0 ((mkInfo c e).nodeAt n) ∧
      ∀ x ∈ (mkInfo c e).post.getD n [], x < 256 := by
  rw [mkInfo_post]; exact (loopOf_inv e).post n

end

end ZkFormal.Near.Render
