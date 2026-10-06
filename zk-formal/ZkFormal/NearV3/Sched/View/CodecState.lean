import ZkFormal.NearV3.Sched.View.CodecEnc
import NearSpec.Bandwidth

/-!
# ZkFormal.NearV3.Sched.View.CodecState — the codec's byte strings as `State.encode`

For an instance block at first row `f` (`N = NN`, `w_k = f + 5 + 24k`, `z = f + 5 + 24N`), with
`rowBytes col r n` the bytes of column `col` on rows `r … r + n − 1` and `rowLE col r n` their
little-endian value:

* **`codec_post_encode`**: the `37 + 24N` post bytes are
  `State.encode ⟨[⟨sid_k, rid_k, afin_k⟩ | k < N], digest⟩` with `sid_k = rowLE bpost w_k 8`,
  `rid_k = rowLE bpost (w_k + 8) 8` (the id bytes received on the `SDL` delay line,
  `codec_post`), `afin_k` the final allowance of record `k` and `digest` the 32 bytes of the
  received `DIGEST` message;
* **`codec_pre_encode`** (`pres = 1`): the pre bytes are
  `State.encode ⟨[⟨sid_k, rid_k, a0_k⟩ | k < N], prevHash⟩` with the same ids,
  `a0_k = rowLE bpre (w_k + 16) 8` and `prevHash = rowBytes bpre z 32` (the SHA input's first
  half, `codec_trailer`);
* `a0_split`: `a0_k = ap_k + 2^24·hi_k` where `ap_k` (= `rowLE bpre (w_k + 16) 3`) is the value
  sent on `SA0` and `hi_k = 0` iff the flag `bF` sent with it is 0 (`codec_rec_msgs`).
-/

namespace ZkFormal.NearV3.Sched.Codec

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E

/-- The bytes of column `col` on rows `r … r + n − 1`. -/
def rowBytes (tr : Trace Fp) (t col : Nat) : Nat → Nat → List UInt8
  | _, 0 => []
  | r, n + 1 => UInt8.ofNat (cv tr t r col) :: rowBytes tr t col (r + 1) n

/-- Their little-endian value. -/
def rowLE (tr : Trace Fp) (t col : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | r, n + 1 => cv tr t r col + 256 * rowLE tr t col (r + 1) n

theorem concatAll_append (a b : List NearSpec.Bytes) :
    NearSpec.concatAll (a ++ b) = NearSpec.concatAll a ++ NearSpec.concatAll b := by
  induction a with
  | nil => rfl
  | cons x a ih => simp only [List.cons_append, NearSpec.concatAll, ih, List.append_assoc]

theorem leN_length (w x : Nat) : (NearSpec.leN w x).length = w := by
  induction w generalizing x with
  | zero => rfl
  | succ w ih => simp only [NearSpec.leN, List.length_cons, ih]

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem rowBytes_add (col r a b : Nat) :
    rowBytes tr t col r (a + b) = rowBytes tr t col r a ++ rowBytes tr t col (r + a) b := by
  induction a generalizing r with
  | zero => simp [rowBytes]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [rowBytes, ih, List.cons_append]
    rw [show r + 1 + a = r + (a + 1) by omega]

theorem rowBytes_eq {col : Nat} : ∀ {r n : Nat} {l : List UInt8}, l.length = n →
    (∀ j, j < n → (l.getD j 0).toNat = cv tr t (r + j) col) → rowBytes tr t col r n = l
  | _, 0, [], _, _ => rfl
  | _, 0, _ :: _, h, _ => by simp at h
  | _, _ + 1, [], h, _ => by simp at h
  | r, n + 1, a :: l, hl, h => by
    simp only [rowBytes]
    have h0 := h 0 (by omega)
    simp only [List.getD_cons_zero, Nat.add_zero] at h0
    rw [← h0, UInt8.ofNat_toNat]
    congr 1
    exact rowBytes_eq (by simpa using hl) (fun j hj => by
      have := h (j + 1) (by omega)
      simp only [List.getD_cons_succ] at this
      rw [this, show r + (j + 1) = r + 1 + j by omega])

theorem rowBytes_le {col : Nat} : ∀ {r n : Nat}, (∀ j, j < n → cv tr t (r + j) col < 256) →
    rowBytes tr t col r n = NearSpec.leN n (rowLE tr t col r n)
  | _, 0, _ => rfl
  | r, n + 1, h => by
    simp only [rowBytes, rowLE, NearSpec.leN]
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [show (cv tr t r col + 256 * rowLE tr t col (r + 1) n) % 256 = cv tr t r col by omega,
      show (cv tr t r col + 256 * rowLE tr t col (r + 1) n) / 256 = rowLE tr t col (r + 1) n by omega]
    congr 1
    exact rowBytes_le (fun j hj => by
      have := h (j + 1) (by omega); rwa [show r + (j + 1) = r + 1 + j by omega] at this)

theorem rowLE_add (col r a b : Nat) :
    rowLE tr t col r (a + b) = rowLE tr t col r a + 256 ^ a * rowLE tr t col (r + a) b := by
  induction a generalizing r with
  | zero => simp [rowLE]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [rowLE, ih]
    rw [show r + 1 + a = r + (a + 1) by omega, Nat.pow_succ]
    generalize rowLE tr t col (r + (a + 1)) b = y
    rw [Nat.mul_add, Nat.add_assoc, Nat.mul_comm (256 ^ a) 256, Nat.mul_assoc]

theorem rowLE_zero_iff {col : Nat} : ∀ {r n : Nat}, rowLE tr t col r n = 0 ↔ ∀ j, j < n → cv tr t (r + j) col = 0
  | _, 0 => by simp [rowLE]
  | r, n + 1 => by
    simp only [rowLE]
    have ih := rowLE_zero_iff (col := col) (r := r + 1) (n := n)
    constructor
    · intro h j hj
      have h1 : cv tr t r col = 0 := by omega
      have h2 : rowLE tr t col (r + 1) n = 0 := by omega
      rcases j with _ | j
      · simpa using h1
      · have := ih.1 h2 j (by omega); rwa [show r + 1 + j = r + (j + 1) by omega] at this
    · intro h
      have h1 := h 0 (by omega); simp only [Nat.add_zero] at h1
      have h2 := ih.2 (fun j hj => by
        have := h (j + 1) (by omega); rwa [show r + (j + 1) = r + 1 + j by omega] at this)
      omega

/-- The link records of the post / pre state. -/
def postLinks (tr : Trace Fp) (t f N : Nat) : List NearSpec.Bandwidth.LinkAllowance :=
  (List.range N).map fun k =>
    ⟨rowLE tr t bpost (f + 5 + 24 * k) 8, rowLE tr t bpost (f + 5 + 24 * k + 8) 8,
      cv tr t (f + 5 + 24 * k + 23) afin⟩

def preLinks (tr : Trace Fp) (t f N : Nat) : List NearSpec.Bandwidth.LinkAllowance :=
  (List.range N).map fun k =>
    ⟨rowLE tr t bpost (f + 5 + 24 * k) 8, rowLE tr t bpost (f + 5 + 24 * k + 8) 8,
      rowLE tr t bpre (f + 5 + 24 * k + 16) 8⟩

/-- Records as concatenated byte blocks. -/
theorem rows_concat {col f : Nat} {B : Nat → List UInt8} :
    ∀ n, (∀ k, k < n → rowBytes tr t col (f + 24 * k) 24 = B k) →
      rowBytes tr t col f (24 * n) = NearSpec.concatAll ((List.range n).map B) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hB
    rw [show 24 * (n + 1) = 24 * n + 24 by omega, rowBytes_add, ih (fun k hk => hB k (by omega)),
      hB n (by omega), List.range_succ,
      List.map_append, concatAll_append]
    simp [NearSpec.concatAll]

theorem getD_map_range {α : Type} (g : Nat → α) (d : α) {n j : Nat} (hj : j < n) :
    ((List.range n).map g).getD j d = g j := by
  simp [List.getD_eq_getElem?_getD, hj]

/-- **Post bytes = `State.encode`.** -/
theorem codec_post_encode (hL : CLocal tr t pub) (hH : tr.height t ≤ 2 ^ 22) {f : Nat}
    (hf : f < tr.height t) (hF : cv tr t f kF = 1) :
    rowBytes tr t bpost f (37 + 24 * cv tr t f NN) =
      NearSpec.Bandwidth.State.encode ⟨postLinks tr t f (cv tr t f NN),
        (List.range 32).map fun j => UInt8.ofNat (cv tr t (f + 5 + 24 * cv tr t f NN) (reg j))⟩ := by
  obtain ⟨-, hN, -, -, -, -, -, RR, -, -, -, -⟩ := codec_block hL hH hf hF
  obtain ⟨-, hhdr, -, halw, -, -, hdig⟩ := codec_post hL hH hf hF
  have enc := enc_rows hL hH hf hF
  have byte : ∀ i, i < 5 + 24 * cv tr t f NN + 32 → cv tr t (f + i) bpost < 256 := fun i hi =>
    (bytes hL (enc i hi).1 (enc i hi).2.1).2.1
  unfold NearSpec.Bandwidth.State.encode postLinks
  simp only [List.length_map, List.length_range]
  rw [show 37 + 24 * cv tr t f NN = 5 + 24 * cv tr t f NN + 32 by omega, rowBytes_add, rowBytes_add]
  congr 1
  congr 1
  · -- header
    apply rowBytes_eq (by simp [NearSpec.u32, leN_length])
    intro j hj
    exact (hhdr j hj).symm
  · -- records
    rw [show f + 5 = f + 5 + 24 * 0 by omega]
    rw [List.map_map]
    apply rows_concat _ (fun k hk => ?_)
    simp only [Function.comp, NearSpec.Bandwidth.LinkAllowance.encode]
    have bk : ∀ o, o < 24 → cv tr t (f + 5 + 24 * k + o) bpost < 256 := fun o ho => by
      have := byte (5 + 24 * k + o) (by have := RR k hk; omega)
      rwa [show f + (5 + 24 * k + o) = f + 5 + 24 * k + o by omega] at this
    obtain ⟨-, hal⟩ := halw k hk
    rw [show f + 5 + 24 * 0 + 24 * k = f + 5 + 24 * k by omega]
    generalize f + 5 + 24 * k = W at bk hal ⊢
    rw [show (24 : Nat) = 8 + 8 + 8 from rfl, rowBytes_add, rowBytes_add]
    have e1 : rowBytes tr t bpost W 8 = NearSpec.u64 (rowLE tr t bpost W 8) :=
      rowBytes_le (fun j hj => bk j (by omega))
    have e2 : rowBytes tr t bpost (W + 8) 8 = NearSpec.u64 (rowLE tr t bpost (W + 8) 8) :=
      rowBytes_le (fun j hj => by rw [Nat.add_assoc]; exact bk (8 + j) (by omega))
    have e3 : rowBytes tr t bpost (W + (8 + 8)) 8 = NearSpec.u64 (cv tr t (W + 23) afin) := by
      apply rowBytes_eq (leN_length 8 _)
      intro j hj
      have := (hal j hj).symm
      unfold NearSpec.u64 at this
      rw [this, show W + 16 + j = W + (8 + 8) + j by omega]
    rw [e1, e2, e3]
  · -- digest
    rw [Nat.add_assoc f 5]
    apply rowBytes_eq (by simp)
    intro j hj
    rw [getD_map_range _ _ hj, ← Nat.add_assoc, hdig j hj]
    simp
    exact (by
      have := byte (5 + 24 * cv tr t f NN + j) (by omega)
      rw [show f + (5 + 24 * cv tr t f NN + j) = f + 5 + 24 * cv tr t f NN + j by omega,
        hdig j hj] at this
      exact this)


theorem rowBytes_congr {c1 c2 : Nat} : ∀ {r n : Nat}, (∀ j, j < n → cv tr t (r + j) c1 = cv tr t (r + j) c2) →
    rowBytes tr t c1 r n = rowBytes tr t c2 r n
  | _, 0, _ => rfl
  | r, n + 1, h => by
    simp only [rowBytes]
    have h0 := h 0 (by omega); simp only [Nat.add_zero] at h0
    rw [h0]
    congr 1
    exact rowBytes_congr (c1 := c1) (c2 := c2) (fun j hj => by
      have := h (j + 1) (by omega); rwa [show r + (j + 1) = r + 1 + j by omega] at this)

/-- **Pre bytes = `State.encode`** (previous state present). -/
theorem codec_pre_encode (hL : CLocal tr t pub) (hH : tr.height t ≤ 2 ^ 22) {f : Nat}
    (hf : f < tr.height t) (hF : cv tr t f kF = 1) (hp : cv tr t f pres = 1) :
    rowBytes tr t bpre f (37 + 24 * cv tr t f NN) =
      NearSpec.Bandwidth.State.encode ⟨preLinks tr t f (cv tr t f NN),
        rowBytes tr t bpre (f + 5 + 24 * cv tr t f NN) 32⟩ := by
  obtain ⟨-, hN, -, -, -, -, -, RR, -, -, -, -⟩ := codec_block hL hH hf hF
  obtain ⟨-, hhdr, -, -, -, -, -⟩ := codec_post hL hH hf hF
  obtain ⟨-, -, -, hph, hpid, hpal, -⟩ := codec_pre hL hH hf hF
  have enc := enc_rows hL hH hf hF
  have byte : ∀ i, i < 5 + 24 * cv tr t f NN + 32 → cv tr t (f + i) bpost < 256 := fun i hi =>
    (bytes hL (enc i hi).1 (enc i hi).2.1).2.1
  unfold NearSpec.Bandwidth.State.encode preLinks
  simp only [List.length_map, List.length_range]
  rw [show 37 + 24 * cv tr t f NN = 5 + 24 * cv tr t f NN + 32 by omega, rowBytes_add, rowBytes_add]
  congr 1
  congr 1
  · -- header
    apply rowBytes_eq (by simp [NearSpec.u32, leN_length])
    intro j hj
    rw [hph j hj, hp, Nat.one_mul]
    exact (hhdr j hj).symm
  · -- records
    rw [show f + 5 = f + 5 + 24 * 0 by omega]
    rw [List.map_map]
    apply rows_concat _ (fun k hk => ?_)
    simp only [Function.comp, NearSpec.Bandwidth.LinkAllowance.encode]
    have bk : ∀ o, o < 24 → cv tr t (f + 5 + 24 * k + o) bpost < 256 := fun o ho => by
      have := byte (5 + 24 * k + o) (by have := RR k hk; omega)
      rwa [show f + (5 + 24 * k + o) = f + 5 + 24 * k + o by omega] at this
    have bp : ∀ o, o < 8 → cv tr t (f + 5 + 24 * k + 16 + o) bpre < 256 := hpal k hk
    have hid : ∀ o, o < 16 → cv tr t (f + 5 + 24 * k + o) bpre = cv tr t (f + 5 + 24 * k + o) bpost :=
      fun o ho => by rw [hpid k hk o ho, hp, Nat.one_mul]
    rw [show f + 5 + 24 * 0 + 24 * k = f + 5 + 24 * k by omega]
    generalize f + 5 + 24 * k = W at bk bp hid ⊢
    rw [show (24 : Nat) = 8 + 8 + 8 from rfl, rowBytes_add, rowBytes_add]
    have e1 : rowBytes tr t bpre W 8 = NearSpec.u64 (rowLE tr t bpost W 8) := by
      rw [rowBytes_congr (c2 := bpost) (fun j hj => hid j (by omega))]
      exact rowBytes_le (fun j hj => bk j (by omega))
    have e2 : rowBytes tr t bpre (W + 8) 8 = NearSpec.u64 (rowLE tr t bpost (W + 8) 8) := by
      rw [rowBytes_congr (c2 := bpost) (fun j hj => by rw [Nat.add_assoc]; exact hid (8 + j) (by omega))]
      exact rowBytes_le (fun j hj => by rw [Nat.add_assoc]; exact bk (8 + j) (by omega))
    have e3 : rowBytes tr t bpre (W + (8 + 8)) 8 = NearSpec.u64 (rowLE tr t bpre (W + 16) 8) :=
      rowBytes_le (fun j hj => bp j hj)
    rw [e1, e2, e3]
  · rw [Nat.add_assoc f 5]

/-- **The previous allowance** `a0_k = ap_k + 2^24·hi_k`, `ap_k < 2^24` the value sent on `SA0`,
`hi_k = 0` iff the flag `bF` sent with it is 0. -/
theorem a0_split (hL : CLocal tr t pub) (hH : tr.height t ≤ 2 ^ 22) {f : Nat}
    (hf : f < tr.height t) (hF : cv tr t f kF = 1) {k : Nat} (hk : k < cv tr t f NN) :
    rowLE tr t bpre (f + 5 + 24 * k + 16) 8 =
        cv tr t (f + 5 + 24 * k + 23) ap + 2 ^ 24 * rowLE tr t bpre (f + 5 + 24 * k + 19) 5 ∧
      cv tr t (f + 5 + 24 * k + 23) ap < 2 ^ 24 ∧
      (cv tr t (f + 5 + 24 * k + 23) bF = 0 ↔ rowLE tr t bpre (f + 5 + 24 * k + 19) 5 = 0) := by
  obtain ⟨-, -, -, -, -, -, -, RR, -⟩ := codec_block hL hH hf hF
  obtain ⟨hap, hbF, -⟩ := alw_walk hL (RR k hk)
  obtain ⟨-, -, -, -, -, hpal, -⟩ := codec_pre hL hH hf hF
  have bp := hpal k hk
  have b0 := bp 0 (by omega); have b1 := bp 1 (by omega); have b2 := bp 2 (by omega)
  simp only [Nat.add_zero] at b0
  rw [show f + 5 + 24 * k + 16 + 1 = f + 5 + 24 * k + 17 by omega] at b1
  rw [show f + 5 + 24 * k + 16 + 2 = f + 5 + 24 * k + 18 by omega] at b2
  have low : rowLE tr t bpre (f + 5 + 24 * k + 16) 3 = cv tr t (f + 5 + 24 * k + 23) ap := by
    rw [hap]; simp only [rowLE]
    rw [show f + 5 + 24 * k + 16 + 1 = f + 5 + 24 * k + 17 by omega,
      show f + 5 + 24 * k + 17 + 1 = f + 5 + 24 * k + 18 by omega]
    omega
  refine ⟨?_, by rw [hap]; omega, ?_⟩
  · rw [show (8 : Nat) = 3 + 5 from rfl, rowLE_add, low,
      show f + 5 + 24 * k + 16 + 3 = f + 5 + 24 * k + 19 by omega]
  · rw [hbF, rowLE_zero_iff]
    constructor
    · intro h j hj
      split at h
      · next hz =>
        obtain ⟨h19, h20, h21, h22, h23⟩ := hz
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with e | e | e | e | e <;> subst e
        · exact h19
        · exact h20
        · exact h21
        · exact h22
        · exact h23
      · exact absurd h (by decide)
    · intro h
      rw [if_pos]
      exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega)⟩

end

end ZkFormal.NearV3.Sched.Codec
