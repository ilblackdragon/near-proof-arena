import StateM5a.RowBrN
import StateM5a.KcChain

/-!
# StateM5a.BrSer — a `BR` row's SHA-256 byte sends spell its node's serialization

`Trie.Br.serBytes` sends the bytes of a branch to `SHA_BYTES` at expression positions (tag, value
ref, bitmap, child hashes at `base + 32·rank_i + b`, memory).  Here, for one row (generic in the
column expressions, so the old node `brOld` and the new node `brNew` are both instances):

* `serF`: the intended serialization as field elements (`blk`: the present slots' 32-byte blocks
  in slot order);
* **`ser_ok`**: every byte send that fires sits at a position `p < |serF|` and carries `serF[p]`
  (rank arithmetic, `blk_get`);
* **`grec_hashed`**: if every entry of `serF` is a byte, the record `gRec` (value, slots, memory
  of the row as `RowBrMsg.brOld` / `RowBrN.brNew` decode them) is all-digest, well formed,
  `Shallow`, and `R.toP.hashOf = sha256 (serF as bytes)`.
-/

namespace StateM5a.BrSer

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrN StateM5a.KcChain

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Blocks of the present slots -/

def cnt (F : Nat → Bool) (n : Nat) : Nat := ((List.range n).map fun i => if F i then 1 else 0).sum

def blk {α : Type} (F : Nat → Bool) (B : Nat → Nat → α) (n : Nat) : List α :=
  (List.range n).flatMap fun i => if F i then (List.range 32).map (B i) else []

section
variable {α : Type} (F : Nat → Bool) (B : Nat → Nat → α)

theorem blk_succ (n : Nat) :
    blk F B (n + 1) = blk F B n ++ (if F n then (List.range 32).map (B n) else []) := by
  simp [blk, List.range_succ, List.flatMap_append]

theorem cnt_succ (n : Nat) : cnt F (n + 1) = cnt F n + (if F n then 1 else 0) := by
  simp [cnt, List.range_succ]

theorem blk_length : ∀ n, (blk F B n).length = 32 * cnt F n
  | 0 => rfl
  | n + 1 => by
    rw [blk_succ, cnt_succ, List.length_append, blk_length n]
    split <;> simp <;> omega

theorem cnt_mono {i : Nat} : ∀ n, i ≤ n → cnt F i ≤ cnt F n
  | 0, h => by rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | n + 1, h => by
    rcases Nat.lt_or_ge i (n + 1) with h' | h'
    · have := cnt_mono (i := i) n (by omega); rw [cnt_succ]; split <;> omega
    · rw [show i = n + 1 by omega]; exact Nat.le_refl _

theorem cnt_le : ∀ n, cnt F n ≤ n
  | 0 => Nat.le_refl _
  | n + 1 => by have := cnt_le n; rw [cnt_succ]; split <;> omega

theorem blk_get {i b : Nat} (hF : F i = true) (hb : b < 32) :
    ∀ n, i < n → (blk F B n)[32 * cnt F i + b]? = some (B i b)
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [blk_succ]
    rcases Nat.lt_or_ge i n with h' | h'
    · have hc : cnt F (i + 1) ≤ cnt F n := cnt_mono F n h'
      rw [cnt_succ, hF] at hc
      simp only [ite_true] at hc
      rw [List.getElem?_append_left (by rw [blk_length]; omega)]
      exact blk_get hF hb n h'
    · obtain rfl : i = n := by omega
      rw [List.getElem?_append_right (by rw [blk_length]; omega), blk_length, hF, if_pos (rfl : true = true),
        show 32 * cnt F i + b - 32 * cnt F i = b by omega, List.getElem?_map, List.getElem?_range hb]
      rfl

end

/-! ## The intended serialization, as field elements -/

section
variable (tr : Trace Fp) (pub : List Fp) (r : Nat)

/-- Slot `i` is present. -/
def flF (fl : Nat → Expr) (i : Nat) : Bool := decide (ev tr 2 r pub (fl i) = 1)

/-- The value ref part (`u32` length, 32 hash bytes) when there is a value. -/
def valF (hv : Expr) (vl vh : Nat → Expr) : List Fp :=
  if ev tr 2 r pub hv = 1 then
    (List.range 4).map (fun t => bE tr pub r (vl t)) ++ (List.range 32).map (fun t => bE tr pub r (vh t))
  else []

/-- **The serialization** a row's byte sends spell. -/
def serF (hv : Expr) (vl vh fl : Nat → Expr) (cb : Nat → Nat → Expr) (mb : Nat → Expr) : List Fp :=
  bE tr pub r (1 + hv) :: (valF tr pub r hv vl vh ++
    (bE tr pub r (Br.bmLo fl) :: bE tr pub r (Br.bmHi fl) ::
      (blk (flF tr pub r fl) (fun i b => bE tr pub r (cb i b)) 16 ++
        (List.range 8).map fun b => bE tr pub r (mb b))))

end

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem valF_length {hv : Expr} {vl vh : Nat → Expr} (hhv : ev tr 2 r pub hv ≤ 1) :
    (valF tr pub r hv vl vh).length = 36 * ev tr 2 r pub hv := by
  unfold valF; split <;> simp <;> omega

theorem ev_n0 : ev tr 2 r pub (0 : Expr) = 0 := ev_const 0
theorem ev_n1 : ev tr 2 r pub (1 : Expr) = 1 := ev_const 1
theorem ev_n2 : ev tr 2 r pub (2 : Expr) = 2 := ev_const 2
theorem ev_n3 : ev tr 2 r pub (3 : Expr) = 3 := ev_const 3
theorem ev_K (n : Nat) : ev tr 2 r pub (K n) = n % P := ev_const n
theorem ev_sm (v : Nat) (e : Expr) : ev tr 2 r pub (sm v e) = (v % P) * ev tr 2 r pub e % P := by
  show ev tr 2 r pub (Expr.mul (.const v) e) = _
  rw [ev_mul, ev_const]

theorem ev_base {e hv : Expr} {c : Nat} (hc : ev tr 2 r pub e = c) (hcP : c < 100)
    (hhv : ev tr 2 r pub hv ≤ 1) : ev tr 2 r pub (e + sm 36 hv) = c + 36 * ev tr 2 r pub hv := by
  rw [ev_hadd, ev_sm, hc, show 36 % P = 36 from rfl, Nat.mod_eq_of_lt (show 36 * ev tr 2 r pub hv < P by omega),
    Nat.mod_eq_of_lt (show c + 36 * ev tr 2 r pub hv < P by omega)]

/-- A rank sum over flag bits counts the present slots. -/
theorem ev_rank {fl : Nat → Expr} (hfl : ∀ i, i < 16 → ev tr 2 r pub (fl i) ≤ 1) :
    ∀ n, n ≤ 16 → ev tr 2 r pub (sumE ((List.range n).map fl)) = cnt (flF tr pub r fl) n := by
  have h : ∀ n, n ≤ 16 → (((List.range n).map fl).map (ev tr 2 r pub)).sum = cnt (flF tr pub r fl) n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [cnt_succ, List.range_succ, List.map_append, List.map_append, List.sum_append, ih (by omega)]
      have := hfl n (by omega)
      simp only [flF, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      by_cases h' : ev tr 2 r pub (fl n) = 1
      · simp [h']
      · simp [h']; omega
  intro n hn
  rw [ev_sumE, h n hn, Nat.mod_eq_of_lt (by have := cnt_le (flF tr pub r fl) n; omega)]

/-- Gate values. -/
theorem ev_gate_one {g x : Expr} (hg : ev tr 2 r pub g = 1) (h : ev tr 2 r pub (g * x) = 1) :
    ev tr 2 r pub x = 1 := by
  rw [ev_hmul, hg, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _)] at h; exact h

section idx
variable {hv : Expr} {vl vh fl mb : Nat → Expr} {cb : Nat → Nat → Expr}

theorem serF_length (hhv : ev tr 2 r pub hv ≤ 1) :
    (serF tr pub r hv vl vh fl cb mb).length = 11 + 36 * ev tr 2 r pub hv + 32 * cnt (flF tr pub r fl) 16 := by
  simp only [serF, List.length_cons, List.length_append, valF_length hhv, blk_length, List.length_map,
    List.length_range]
  omega

theorem serF_val {k : Nat} (hk : k < 36 * ev tr 2 r pub hv) (hhv : ev tr 2 r pub hv ≤ 1) :
    (serF tr pub r hv vl vh fl cb mb)[1 + k]? = (valF tr pub r hv vl vh)[k]? := by
  rw [Nat.add_comm, serF, List.getElem?_cons_succ, List.getElem?_append_left (by rw [valF_length hhv]; exact hk)]

theorem serF_rest {k : Nat} (hhv : ev tr 2 r pub hv ≤ 1) :
    (serF tr pub r hv vl vh fl cb mb)[1 + 36 * ev tr 2 r pub hv + k]? =
      (bE tr pub r (Br.bmLo fl) :: bE tr pub r (Br.bmHi fl) ::
        (blk (flF tr pub r fl) (fun i b => bE tr pub r (cb i b)) 16 ++
          (List.range 8).map fun b => bE tr pub r (mb b)))[k]? := by
  rw [show 1 + 36 * ev tr 2 r pub hv + k = (36 * ev tr 2 r pub hv + k) + 1 by omega, serF,
    List.getElem?_cons_succ, List.getElem?_append_right (by rw [valF_length hhv]; omega), valF_length hhv,
    show 36 * ev tr 2 r pub hv + k - 36 * ev tr 2 r pub hv = k by omega]

end idx

theorem ser_ok {id g gv hv : Expr} {vl vh fl mb : Nat → Expr} {cb : Nat → Nat → Expr}
    (hg : ev tr 2 r pub g = 1) (hgv : ev tr 2 r pub gv = 1 → ev tr 2 r pub hv = 1)
    (hhv : ev tr 2 r pub hv ≤ 1) (hfl : ∀ i, i < 16 → ev tr 2 r pub (fl i) ≤ 1)
    {x : Interaction} (hx : x ∈ Br.serBytes id g gv hv vl vh fl (fun i => sumE ((List.range i).map fl)) cb mb)
    (hp : 0 < x.multNat tr 2 r pub) :
    ∃ pe ve, x.msg = [id, pe, ve] ∧ ev tr 2 r pub pe < (serF tr pub r hv vl vh fl cb mb).length ∧
      (serF tr pub r hv vl vh fl cb mb)[ev tr 2 r pub pe]? = some (bE tr pub r ve) := by
  unfold Br.serBytes at hx
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false] at hx
  have hlen := serF_length (vl := vl) (vh := vh) (cb := cb) (mb := mb) (fl := fl) hhv
  have hc16 := cnt_le (flF tr pub r fl) 16
  have hrk := ev_rank hfl
  rcases hx with ((((rfl | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) | (rfl | rfl)) | ⟨a, ha, b, hb, rfl⟩) | ⟨b, hb, rfl⟩
  · refine ⟨_, _, rfl, ?_, ?_⟩
    · rw [ev_n0, hlen]; omega
    · rw [ev_n0]; rfl
  · have h1 := hgv (eval_one_ev (multNat_one_bit rfl hp))
    refine ⟨_, _, rfl, ?_, ?_⟩
    · rw [ev_K, hlen]; omega
    · rw [ev_K, Nat.mod_eq_of_lt (by omega), serF_val (by omega) hhv]
      simp only [valF, h1, ite_true]
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range ha]; rfl
  · have h1 := hgv (eval_one_ev (multNat_one_bit rfl hp))
    refine ⟨_, _, rfl, ?_, ?_⟩
    · rw [ev_K, hlen]; omega
    · rw [ev_K, Nat.mod_eq_of_lt (by omega), show 5 + a = 1 + (4 + a) by omega, serF_val (by omega) hhv]
      simp only [valF, h1, ite_true]
      rw [List.getElem?_append_right (by simp), List.getElem?_map]
      simp only [List.length_map, List.length_range, show 4 + a - 4 = a by omega, List.getElem?_range ha]; rfl
  · have he := ev_base ev_n1 (by omega) hhv
    refine ⟨_, _, rfl, ?_, ?_⟩
    · rw [he, hlen]; omega
    · rw [he, show 1 + 36 * ev tr 2 r pub hv = 1 + 36 * ev tr 2 r pub hv + 0 by omega, serF_rest hhv]; rfl
  · have he := ev_base ev_n2 (by omega) hhv
    refine ⟨_, _, rfl, ?_, ?_⟩
    · rw [he, hlen]; omega
    · rw [he, show 2 + 36 * ev tr 2 r pub hv = 1 + 36 * ev tr 2 r pub hv + 1 by omega, serF_rest hhv]; rfl
  · have hf := ev_gate_one hg (eval_one_ev (multNat_one_bit rfl hp))
    have hF : flF tr pub r fl a = true := by simp [flF, hf]
    have hr := hrk a (by omega)
    have hcl : cnt (flF tr pub r fl) (a + 1) ≤ cnt (flF tr pub r fl) 16 := cnt_mono _ 16 (by omega)
    rw [cnt_succ, hF] at hcl
    simp only [ite_true] at hcl
    have he : ev tr 2 r pub (3 + sm 36 hv + sm 32 (sumE (List.map fl (List.range a))) + K b) =
        1 + 36 * ev tr 2 r pub hv + (32 * cnt (flF tr pub r fl) a + b + 1 + 1) := by
      rw [ev_hadd, ev_hadd, ev_base ev_n3 (by omega) hhv, ev_sm, ev_K, hr]
      rw [show 32 % P = 32 from rfl, Nat.mod_eq_of_lt (show 32 * cnt (flF tr pub r fl) a < P by omega),
        Nat.mod_eq_of_lt (show b < P by omega)]
      omega
    refine ⟨_, _, rfl, ?_, ?_⟩
    · rw [he, hlen]; omega
    · rw [he, serF_rest hhv, List.getElem?_cons_succ, List.getElem?_cons_succ,
        List.getElem?_append_left (by rw [blk_length]; omega), blk_get _ _ hF hb 16 ha]
  · have hr := hrk 16 (Nat.le_refl _)
    have he : ev tr 2 r pub (3 + sm 36 hv + sm 32 (sumE (List.map fl (List.range 16))) + K b) =
        1 + 36 * ev tr 2 r pub hv + (32 * cnt (flF tr pub r fl) 16 + b + 1 + 1) := by
      rw [ev_hadd, ev_hadd, ev_base ev_n3 (by omega) hhv, ev_sm, ev_K, hr]
      rw [show 32 % P = 32 from rfl, Nat.mod_eq_of_lt (show 32 * cnt (flF tr pub r fl) 16 < P by omega),
        Nat.mod_eq_of_lt (show b < P by omega)]
      omega
    refine ⟨_, _, rfl, ?_, ?_⟩
    · rw [he, hlen]; omega
    · rw [he, serF_rest hhv, List.getElem?_cons_succ, List.getElem?_cons_succ,
        List.getElem?_append_right (by rw [blk_length]; omega), blk_length,
        show 32 * cnt (flF tr pub r fl) 16 + b - 32 * cnt (flF tr pub r fl) 16 = b by omega,
        List.getElem?_map, List.getElem?_range hb]; rfl

end

/-! ## Slots of a `kidsFrom` record, as the spec's node sees them -/

section kids
variable (fl : Nat → Nat) (rf : Nat → Ref)

def bmN : Nat → Nat → Nat → Nat
  | _, 0, _ => 0
  | i, k + 1, j => 2 ^ j * fl i + bmN (i + 1) k (j + 1)

theorem kf_bitmap : ∀ k i j, (∀ m, m < k → fl (i + m) ≤ 1) →
    kidsBitmap (RowBr.kidsFrom fl rf i k).toK j = bmN fl i k j
  | 0, _, _, _ => rfl
  | k + 1, i, j, h => by
    have ih := kf_bitmap k (i + 1) (j + 1) (fun m hm => by rw [show i + 1 + m = i + (m + 1) by omega]; exact h _ (by omega))
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    simp only [RowBr.kidsFrom, bmN]
    by_cases e : fl i = 1
    · simp only [e, ↓reduceIte, RKids.toK, kidsBitmap, ih, e, Nat.mul_one]
    · have e0 : fl i = 0 := by omega
      simp only [e, ↓reduceIte]
      simp only [RKids.toK, kidsBitmap, ih, e0, Nat.mul_zero, Nat.zero_add]

theorem kf_hashes : ∀ k i, Kids.hashes (RowBr.kidsFrom fl rf i k).toK =
    (List.range' i k).flatMap (fun j => if fl j = 1 then (rf j).toP.hashOf else [])
  | 0, _ => rfl
  | k + 1, i => by
    simp only [RowBr.kidsFrom, List.range'_succ, List.flatMap_cons]
    by_cases e : fl i = 1
    · simp only [e, ↓reduceIte, RKids.toK, Kids.hashes, kf_hashes k (i + 1)]
    · simp only [e, ↓reduceIte, RKids.toK, Kids.hashes, kf_hashes k (i + 1), List.nil_append]

theorem kf_wf : ∀ k i, (∀ m, m < k → fl (i + m) = 1 → (rf (i + m)).toP.wf = true) →
    Kids.wf (RowBr.kidsFrom fl rf i k).toK k = true
  | 0, _, _ => rfl
  | k + 1, i, h => by
    have ih := kf_wf k (i + 1) (fun m hm e => by
      rw [show i + 1 + m = i + (m + 1) by omega] at e ⊢; exact h _ (by omega) e)
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    simp only [RowBr.kidsFrom]
    by_cases e : fl i = 1
    · simp [e, RKids.toK, Kids.wf, h0 e, ih]
    · simp [e, RKids.toK, Kids.wf, ih]

theorem kf_allDig : ∀ k i, (∀ m, m < k → fl (i + m) = 1 → (rf (i + m)).IsDig) → (RowBr.kidsFrom fl rf i k).AllDig
  | 0, _, _ => trivial
  | k + 1, i, h => by
    have ih := kf_allDig k (i + 1) (fun m hm e => by
      rw [show i + 1 + m = i + (m + 1) by omega] at e ⊢; exact h _ (by omega) e)
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    simp only [RowBr.kidsFrom]
    by_cases e : fl i = 1
    · simp only [e, ↓reduceIte]; exact ⟨h0 e, ih⟩
    · simp only [e, ↓reduceIte]; exact ih

end kids

theorem toK_at : ∀ (x : RKids) (n : Nat) (c : PTrie), Kids.at x.toK n = some c → ∃ h, c = .hash h
  | .nil, _, _, e => by simp [RKids.toK, Kids.at] at e
  | .none _, 0, _, e => by simp [RKids.toK, Kids.at] at e
  | .none x, n + 1, c, e => toK_at x n c e
  | .some a _, 0, c, e => by
    simp only [RKids.toK, Kids.at, Option.some.injEq] at e
    subst e; cases a <;> exact ⟨_, rfl⟩
  | .some _ x, n + 1, c, e => toK_at x n c e

/-! ## Byte encodings -/

theorem limbBytes_append : ∀ (a b : List Nat), Tape.limbBytes (a ++ b) = Tape.limbBytes a ++ Tape.limbBytes b
  | [], _ => rfl
  | x :: a, b => by simp only [List.cons_append, Tape.limbBytes, limbBytes_append a b]

theorem limbBytes_pack (a : Nat → Nat) : ∀ n, (∀ j, j < 2 * n → a j < 256) →
    Tape.limbBytes ((List.range n).map fun i => 256 * a (2 * i) + a (2 * i + 1)) =
      (List.range (2 * n)).map fun j => UInt8.ofNat (a j)
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.map_append, limbBytes_append, limbBytes_pack a n (fun j hj => h j (by omega)),
      show 2 * (n + 1) = 2 * n + 1 + 1 by omega, List.range_succ, List.range_succ, List.map_append,
      List.map_append, List.append_assoc]
    have h1 := h (2 * n) (by omega)
    have h2 := h (2 * n + 1) (by omega)
    simp only [List.map_cons, List.map_nil, Tape.limbBytes, List.singleton_append]
    rw [show (256 * a (2 * n) + a (2 * n + 1)) / 256 = a (2 * n) by omega,
      show (256 * a (2 * n) + a (2 * n + 1)) % 256 = a (2 * n + 1) by omega]

theorem leN_cons (w a x : Nat) (ha : a < 256) : leN (w + 1) (a + 256 * x) = UInt8.ofNat a :: leN w x := by
  simp only [leN]
  rw [show (a + 256 * x) % 256 = a by omega, show (a + 256 * x) / 256 = x by omega]

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem ev_byte2 (a b : Expr) (ha : ev tr 2 r pub a < 256) (hb : ev tr 2 r pub b < 256) :
    ev tr 2 r pub (K 256 * a + b) = 256 * ev tr 2 r pub a + ev tr 2 r pub b := by
  rw [ev_hadd, ev_hmul, ev_K, show 256 % P = 256 from rfl,
    Nat.mod_eq_of_lt (show 256 * ev tr 2 r pub a < P by omega),
    Nat.mod_eq_of_lt (show 256 * ev tr 2 r pub a + ev tr 2 r pub b < P by omega)]

theorem ev_limb16 (v : Nat → Expr) (k : Nat) (ha : ev tr 2 r pub (v (2 * k)) < 256)
    (hb : ev tr 2 r pub (v (2 * k + 1)) < 256) :
    ev tr 2 r pub (limb16 v k) = ev tr 2 r pub (v (2 * k)) + 256 * ev tr 2 r pub (v (2 * k + 1)) := by
  unfold limb16
  rw [ev_hadd, ev_hmul, ev_K, show 256 % P = 256 from rfl,
    Nat.mod_eq_of_lt (show 256 * ev tr 2 r pub (v (2 * k + 1)) < P by omega),
    Nat.mod_eq_of_lt (show ev tr 2 r pub (v (2 * k)) + 256 * ev tr 2 r pub (v (2 * k + 1)) < P by omega)]

/-- 32 bytes packed in 16-bit limbs and unpacked. -/
theorem bytesOf_pack2 (v : Nat → Expr) (h : ∀ j, j < 32 → ev tr 2 r pub (v j) < 256) :
    bytesOf ((pack2 v).map (bE tr pub r)) = (List.range 32).map fun j => UInt8.ofNat (ev tr 2 r pub (v j)) := by
  unfold bytesOf pack2
  rw [List.map_map, List.map_map]
  have e : (List.range 16).map ((Fp.toNat ∘ bE tr pub r) ∘ fun i => K 256 * v (2 * i) + v (2 * i + 1)) =
      (List.range 16).map fun i => 256 * ev tr 2 r pub (v (2 * i)) + ev tr 2 r pub (v (2 * i + 1)) := by
    apply List.map_congr_left
    intro i hi
    have := List.mem_range.1 hi
    exact ev_byte2 _ _ (h _ (by omega)) (h _ (by omega))
  rw [e, limbBytes_pack (fun j => ev tr 2 r pub (v j)) 16 h]

theorem ev_smb (c : Nat) (x : Expr) (hc : c < 65536) (hx : ev tr 2 r pub x ≤ 1) :
    ev tr 2 r pub (sm c x) = c * ev tr 2 r pub x := by
  rw [ev_sm, Nat.mod_eq_of_lt (show c < P by omega), Nat.mod_eq_of_lt (show c * ev tr 2 r pub x < P by
    have := Nat.mul_le_mul_left c hx; omega)]

theorem sum_bits_lt (f : Nat → Nat) (hf : ∀ i, f i ≤ 1) : ∀ n, ((List.range n).map fun i => 2 ^ i * f i).sum < 2 ^ n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append]
    have := sum_bits_lt f hf n
    have h1 := Nat.mul_le_mul_left (2 ^ n) (hf n)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.pow_succ]
    omega

/-- A bitmap byte. -/
theorem ev_bm (x : Nat → Expr) (hx : ∀ i, i < 8 → ev tr 2 r pub (x i) ≤ 1) :
    ev tr 2 r pub (sumE ((List.range 8).map fun i => sm (2 ^ i) (x i))) =
      ((List.range 8).map fun i => 2 ^ i * (if i < 8 then ev tr 2 r pub (x i) else 0)).sum := by
  rw [ev_sumE, List.map_map]
  have e : (List.range 8).map (ev tr 2 r pub ∘ fun i => sm (2 ^ i) (x i)) =
      (List.range 8).map fun i => 2 ^ i * (if i < 8 then ev tr 2 r pub (x i) else 0) := by
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.1 hi
    simp only [Function.comp, hi', ↓reduceIte]
    exact ev_smb _ _ (by have := Nat.pow_lt_pow_right (a := 2) (by omega) hi'; omega) (hx i hi')
  rw [e]
  apply Nat.mod_eq_of_lt
  have := sum_bits_lt (fun i => if i < 8 then ev tr 2 r pub (x i) else 0) (fun i => by
    split
    · exact hx i ‹_›
    · omega) 8
  omega

end

theorem bmN_sum (f : Nat → Nat) : ∀ k i j, bmN f i k j = ((List.range k).map fun m => 2 ^ (j + m) * f (i + m)).sum
  | 0, _, _ => rfl
  | k + 1, i, j => by
    rw [bmN, bmN_sum f k (i + 1) (j + 1), List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    simp only [Nat.add_zero]
    congr 2
    apply List.map_congr_left
    intro m _
    simp only [Function.comp, Nat.succ_eq_add_one]
    rw [show j + 1 + m = j + (m + 1) by omega, show i + 1 + m = i + (m + 1) by omega]

theorem bm_split (f : Nat → Nat) : ((List.range 16).map fun m => 2 ^ (0 + m) * f (0 + m)).sum =
    ((List.range 8).map fun i => 2 ^ i * (if i < 8 then f i else 0)).sum +
      256 * ((List.range 8).map fun i => 2 ^ i * (if i < 8 then f (i + 8) else 0)).sum := by
  simp [List.range_succ]
  omega

/-! ## The record a row's columns decode to -/

section
variable (tr : Trace Fp) (pub : List Fp) (r : Nat)

/-- A branch record from the row's value / slot / memory columns (`brOld`, `brNew`). -/
def gRec (hv : Expr) (vl vh fl isn : Nat → Expr) (cb : Nat → Nat → Expr) (mb : Nat → Expr) : Rec :=
  .branch (if ev tr 2 r pub hv = 1 then
      some (.ref ((bE tr pub r (limb16 vl 0)).toNat + 65536 * (bE tr pub r (limb16 vl 1)).toNat)
        (bytesOf ((pack2 vh).map (bE tr pub r))))
    else none)
    (RowBr.kidsFrom (fun i => ev tr 2 r pub (fl i))
      (fun i => refOf (bE tr pub r (isn i)) ((pack2 (cb i)).map (bE tr pub r))) 0 16)
    (le4 (((List.range 4).map fun k => limb16 mb k).map (bE tr pub r)))

theorem brOld_eq : brOld tr pub r = gRec tr pub r (Br.c "hasv") (fun t => Br.c "vl" t) (fun t => Br.c "vh" t)
    (fun i => Br.c "f" i) (fun i => Br.c "isn" i) Br.ch (fun b => Br.c "mem" b) := rfl

theorem brNew_eq : brNew tr pub r = gRec tr pub r (Br.c "nhv") (fun t => Br.c "nvl" t) (fun t => Br.c "nvh" t)
    (fun i => Br.c "nf" i) Br.nisn Br.newch (fun b => Br.c "nmem" b) := rfl

end

/-! ## A hashed record -/

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}
variable {hv : Expr} {vl vh fl isn mb : Nat → Expr} {cb : Nat → Nat → Expr}

/-- The byte facts carried by a serialization of bytes. -/
structure SerBytes (tr : Trace Fp) (pub : List Fp) (r : Nat) (hv : Expr) (vl vh fl : Nat → Expr)
    (cb : Nat → Nat → Expr) (mb : Nat → Expr) : Prop where
  vl : ev tr 2 r pub hv = 1 → ∀ t, t < 4 → ev tr 2 r pub (vl t) < 256
  vh : ev tr 2 r pub hv = 1 → ∀ t, t < 32 → ev tr 2 r pub (vh t) < 256
  lo : ev tr 2 r pub (Br.bmLo fl) < 256
  hi : ev tr 2 r pub (Br.bmHi fl) < 256
  cb : ∀ i, i < 16 → ev tr 2 r pub (fl i) = 1 → ∀ b, b < 32 → ev tr 2 r pub (cb i b) < 256
  mb : ∀ b, b < 8 → ev tr 2 r pub (mb b) < 256

theorem mem_serF_val {x : Fp} (h : x ∈ valF tr pub r hv vl vh) : x ∈ serF tr pub r hv vl vh fl cb mb :=
  List.mem_cons_of_mem _ (List.mem_append_left _ h)

theorem mem_serF_tail {x : Fp}
    (h : x ∈ blk (flF tr pub r fl) (fun i b => bE tr pub r (cb i b)) 16 ++ (List.range 8).map fun b => bE tr pub r (mb b)) :
    x ∈ serF tr pub r hv vl vh fl cb mb :=
  List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))

theorem serBytes_of (hS : ∀ x ∈ serF tr pub r hv vl vh fl cb mb, x.toNat < 256) :
    SerBytes tr pub r hv vl vh fl cb mb where
  vl h t ht := hS _ (mem_serF_val (by
    simp only [valF, h, ↓reduceIte]; exact List.mem_append_left _ (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩)))
  vh h t ht := hS _ (mem_serF_val (by
    simp only [valF, h, ↓reduceIte]; exact List.mem_append_right _ (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩)))
  lo := hS _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_self ..)))
  hi := hS _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  cb i hi hf b hb := hS _ (mem_serF_tail (List.mem_append_left _ (by
    simp only [blk, List.mem_flatMap, List.mem_range]
    exact ⟨i, hi, by simp only [flF, hf, decide_true, ↓reduceIte]; exact List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩⟩)))
  mb b hb := hS _ (mem_serF_tail (List.mem_append_right _ (List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩)))

end

/-! ## The hash of the record -/

theorem refOf_dig' (fl : Fp) (ls : List Fp) (hl : ls.length = 16) (h : fl.toNat = 0) :
    refOf fl ls = .dig (bytesOf ls) := by
  simp only [refOf, Tape.refDec, List.getD_cons_zero, h, ↓reduceIte, List.drop_succ_cons, List.drop_zero,
    List.take_of_length_le (show ls.length ≤ 16 by omega), bytesOf]

theorem limbBytes_len' : ∀ l : List Nat, (Tape.limbBytes l).length = 2 * l.length
  | [] => rfl
  | _ :: l => by simp only [Tape.limbBytes, List.length_cons, limbBytes_len' l]; omega

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem leN8 (a : Nat → Nat) (h : ∀ b, b < 8 → a b < 256) :
    leN 8 (a 0 + 256 * a 1 + 65536 * a 2 + 16777216 * a 3 + 4294967296 * a 4 + 1099511627776 * a 5 +
      281474976710656 * a 6 + 72057594037927936 * a 7) = (List.range 8).map fun b => UInt8.ofNat (a b) := by
  rw [show a 0 + 256 * a 1 + 65536 * a 2 + 16777216 * a 3 + 4294967296 * a 4 + 1099511627776 * a 5 +
      281474976710656 * a 6 + 72057594037927936 * a 7 =
      a 0 + 256 * (a 1 + 256 * (a 2 + 256 * (a 3 + 256 * (a 4 + 256 * (a 5 + 256 * (a 6 + 256 * (a 7 + 256 * 0))))))) by
    omega]
  rw [leN_cons _ _ _ (h 0 (by omega)), leN_cons _ _ _ (h 1 (by omega)), leN_cons _ _ _ (h 2 (by omega)),
    leN_cons _ _ _ (h 3 (by omega)), leN_cons _ _ _ (h 4 (by omega)), leN_cons _ _ _ (h 5 (by omega)),
    leN_cons _ _ _ (h 6 (by omega)), leN_cons _ _ _ (h 7 (by omega))]
  rfl

theorem leN4 (a : Nat → Nat) (h : ∀ b, b < 4 → a b < 256) :
    leN 4 (a 0 + 256 * a 1 + 65536 * (a 2 + 256 * a 3)) = (List.range 4).map fun b => UInt8.ofNat (a b) := by
  rw [show a 0 + 256 * a 1 + 65536 * (a 2 + 256 * a 3) = a 0 + 256 * (a 1 + 256 * (a 2 + 256 * (a 3 + 256 * 0))) by
    omega]
  rw [leN_cons _ _ _ (h 0 (by omega)), leN_cons _ _ _ (h 1 (by omega)), leN_cons _ _ _ (h 2 (by omega)),
    leN_cons _ _ _ (h 3 (by omega))]
  rfl

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}
variable {hv : Expr} {vl vh fl isn mb : Nat → Expr} {cb : Nat → Nat → Expr}

theorem le4_mem (hB : SerBytes tr pub r hv vl vh fl cb mb) :
    le4 (((List.range 4).map fun k => limb16 mb k).map (bE tr pub r)) =
      ev tr 2 r pub (mb 0) + 256 * ev tr 2 r pub (mb 1) + 65536 * ev tr 2 r pub (mb 2) +
        16777216 * ev tr 2 r pub (mb 3) + 4294967296 * ev tr 2 r pub (mb 4) +
        1099511627776 * ev tr 2 r pub (mb 5) + 281474976710656 * ev tr 2 r pub (mb 6) +
        72057594037927936 * ev tr 2 r pub (mb 7) := by
  show ev tr 2 r pub (limb16 mb 0) + 65536 * ev tr 2 r pub (limb16 mb 1) + 4294967296 * ev tr 2 r pub (limb16 mb 2) +
    281474976710656 * ev tr 2 r pub (limb16 mb 3) = _
  rw [ev_limb16 mb 0 (hB.mb _ (by omega)) (hB.mb _ (by omega)), ev_limb16 mb 1 (hB.mb _ (by omega)) (hB.mb _ (by omega)),
    ev_limb16 mb 2 (hB.mb _ (by omega)) (hB.mb _ (by omega)), ev_limb16 mb 3 (hB.mb _ (by omega)) (hB.mb _ (by omega))]
  simp only [Nat.reduceMul, Nat.reduceAdd]
  omega

theorem u64_mem (hB : SerBytes tr pub r hv vl vh fl cb mb) :
    u64 (le4 (((List.range 4).map fun k => limb16 mb k).map (bE tr pub r))) =
      ((List.range 8).map fun b => bE tr pub r (mb b)).map fun x => UInt8.ofNat x.toNat := by
  rw [le4_mem hB, u64, leN8 (fun b => ev tr 2 r pub (mb b)) hB.mb, List.map_map]
  rfl

theorem vlen_val (hB : SerBytes tr pub r hv vl vh fl cb mb) (h1 : ev tr 2 r pub hv = 1) :
    (bE tr pub r (limb16 vl 0)).toNat + 65536 * (bE tr pub r (limb16 vl 1)).toNat =
      ev tr 2 r pub (vl 0) + 256 * ev tr 2 r pub (vl 1) + 65536 * (ev tr 2 r pub (vl 2) + 256 * ev tr 2 r pub (vl 3)) := by
  show ev tr 2 r pub (limb16 vl 0) + 65536 * ev tr 2 r pub (limb16 vl 1) = _
  rw [ev_limb16 vl 0 (hB.vl h1 _ (by omega)) (hB.vl h1 _ (by omega)),
    ev_limb16 vl 1 (hB.vl h1 _ (by omega)) (hB.vl h1 _ (by omega))]

theorem valueRef_val (hB : SerBytes tr pub r hv vl vh fl cb mb) (h1 : ev tr 2 r pub hv = 1) :
    Slot.valueRef (.ref ((bE tr pub r (limb16 vl 0)).toNat + 65536 * (bE tr pub r (limb16 vl 1)).toNat)
      (bytesOf ((pack2 vh).map (bE tr pub r)))) =
      (valF tr pub r hv vl vh).map fun x => UInt8.ofNat x.toNat := by
  simp only [Slot.valueRef, valF, h1, ↓reduceIte, List.map_append, List.map_map]
  rw [vlen_val hB h1, u32, leN4 (fun b => ev tr 2 r pub (vl b)) (hB.vl h1), bytesOf_pack2 vh (hB.vh h1)]
  rfl

theorem bitmap_val (hfl : ∀ i, i < 16 → ev tr 2 r pub (fl i) ≤ 1) (hB : SerBytes tr pub r hv vl vh fl cb mb)
    (rf : Nat → Ref) :
    u16 (kidsBitmap (RowBr.kidsFrom (fun i => ev tr 2 r pub (fl i)) rf 0 16).toK 0) =
      [UInt8.ofNat (ev tr 2 r pub (Br.bmLo fl)), UInt8.ofNat (ev tr 2 r pub (Br.bmHi fl))] := by
  rw [kf_bitmap _ _ 16 0 0 (fun m hm => hfl _ (by omega)), bmN_sum, bm_split (fun i => ev tr 2 r pub (fl i))]
  have elo : ev tr 2 r pub (Br.bmLo fl) = _ := ev_bm fl (fun i hi => hfl i (by omega))
  have ehi : ev tr 2 r pub (Br.bmHi fl) = _ := ev_bm (fun i => fl (i + 8)) (fun i hi => hfl _ (by omega))
  have hlo := hB.lo
  have hhi := hB.hi
  rw [elo] at hlo ⊢
  rw [ehi] at hhi ⊢
  rw [u16, leN_cons _ _ _ hlo, show 1 = 0 + 1 from rfl, leN]
  simp only [leN, Nat.mod_eq_of_lt hhi]

theorem hashes_val (hfl : ∀ i, i < 16 → ev tr 2 r pub (fl i) ≤ 1)
    (hisn : ∀ i, i < 16 → ev tr 2 r pub (fl i) = 1 → ev tr 2 r pub (isn i) = 0)
    (hB : SerBytes tr pub r hv vl vh fl cb mb) :
    Kids.hashes (RowBr.kidsFrom (fun i => ev tr 2 r pub (fl i))
      (fun i => refOf (bE tr pub r (isn i)) ((pack2 (cb i)).map (bE tr pub r))) 0 16).toK =
      (blk (flF tr pub r fl) (fun i b => bE tr pub r (cb i b)) 16).map fun x => UInt8.ofNat x.toNat := by
  rw [kf_hashes, blk, List.map_flatMap, List.range_eq_range']
  apply flatMap_congr_mem
  intro j hj
  have hj' : j < 16 := by simp at hj; omega
  by_cases e : ev tr 2 r pub (fl j) = 1
  · have hF : flF tr pub r fl j = true := by simp [flF, e]
    simp only [e, hF, ↓reduceIte]
    rw [refOf_dig' _ _ (by simp [pack2]) (hisn j hj' e)]
    simp only [Ref.toP, PTrie.hashOf]
    rw [bytesOf_pack2 _ (hB.cb j hj' e), List.map_map]
    rfl
  · have hF : flF tr pub r fl j = false := by simp [flF, e]
    simp only [e, hF, ↓reduceIte, Bool.false_eq_true, List.map_nil]

/-- **A record whose serialization bytes are `serF`** is all-digest, well formed, `Shallow`, and
hashes to `sha256` of those bytes. -/
theorem grec_hashed (hhv : ev tr 2 r pub hv ≤ 1) (hfl : ∀ i, i < 16 → ev tr 2 r pub (fl i) ≤ 1)
    (hisn : ∀ i, i < 16 → ev tr 2 r pub (fl i) = 1 → ev tr 2 r pub (isn i) = 0)
    (hB : SerBytes tr pub r hv vl vh fl cb mb) :
    Hashed (gRec tr pub r hv vl vh fl isn cb mb)
      (sha256 ((serF tr pub r hv vl vh fl cb mb).map fun x => UInt8.ofNat x.toNat)) := by
  have hdig : ∀ m, m < 16 → ev tr 2 r pub (fl (0 + m)) = 1 →
      refOf (bE tr pub r (isn (0 + m))) ((pack2 (cb (0 + m))).map (bE tr pub r)) =
        .dig (bytesOf ((pack2 (cb (0 + m))).map (bE tr pub r))) := fun m hm e =>
    refOf_dig' _ _ (by simp [pack2]) (hisn _ (by omega) e)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact kf_allDig _ _ 16 0 (fun m hm e => by rw [hdig m hm e]; trivial)
  · have hk := kf_wf (fun i => ev tr 2 r pub (fl i))
      (fun i => refOf (bE tr pub r (isn i)) ((pack2 (cb i)).map (bE tr pub r))) 16 0 (fun m hm e => by
        rw [hdig m hm e]; simp [Ref.toP, PTrie.wf, bytesOf, limbBytes_len', pack2])
    have hmem : le4 (((List.range 4).map fun k => limb16 mb k).map (bE tr pub r)) < 18446744073709551616 := by
      rw [le4_mem hB]
      have hm := hB.mb
      have := hm 0 (by omega); have := hm 1 (by omega); have := hm 2 (by omega); have := hm 3 (by omega)
      have := hm 4 (by omega); have := hm 5 (by omega); have := hm 6 (by omega); have := hm 7 (by omega)
      omega
    by_cases h1 : ev tr 2 r pub hv = 1
    · have hv := hB.vl h1
      have := hv 0 (by omega); have := hv 1 (by omega); have := hv 2 (by omega); have := hv 3 (by omega)
      have hl : (bE tr pub r (limb16 vl 0)).toNat + 65536 * (bE tr pub r (limb16 vl 1)).toNat < 4294967296 := by
        rw [vlen_val hB h1]; omega
      simp only [gRec, h1, ↓reduceIte, Rec.toP, PTrie.wf, slotOk, hk, hl, hmem]
      simp [bytesOf, limbBytes_len', pack2]
    · simp only [gRec, h1, ↓reduceIte, Rec.toP, PTrie.wf, hk, hmem]
      rfl
  · refine ⟨fun sl hs => ?_, fun n c h => toK_at _ n c h⟩
    split at hs
    · cases hs; exact ⟨_, _, rfl⟩
    · cases hs
  · rcases Nat.lt_or_ge (ev tr 2 r pub hv) 1 with h0 | h1
    · have h0' : ev tr 2 r pub hv = 0 := by omega
      have hne : ¬ ev tr 2 r pub hv = 1 := by omega
      have e1 : ev tr 2 r pub (1 + hv) = 1 := by rw [ev_hadd, ev_n1, h0']
      simp only [gRec, hne, ↓reduceIte, Rec.toP, PTrie.hashOf]
      congr 1
      simp only [serF, valF, hne, ↓reduceIte, List.map_cons, List.map_append, List.map_nil, List.nil_append,
        bitmap_val hfl hB, hashes_val hfl hisn hB, u64_mem hB]
      show _ = UInt8.ofNat (ev tr 2 r pub (1 + hv)) :: _
      rw [e1]
      rfl
    · have h1' : ev tr 2 r pub hv = 1 := by omega
      have e1 : ev tr 2 r pub (1 + hv) = 2 := by rw [ev_hadd, ev_n1, h1']
      simp only [gRec, h1', ↓reduceIte, Rec.toP, PTrie.hashOf]
      congr 1
      rw [valueRef_val hB h1']
      simp only [serF, List.map_cons, List.map_append,
        bitmap_val hfl hB, hashes_val hfl hisn hB, u64_mem hB]
      show _ = UInt8.ofNat (ev tr 2 r pub (1 + hv)) :: _
      rw [e1]
      simp only [List.cons_append, List.append_assoc, List.nil_append]
      rfl

end

end StateM5a.BrSer
