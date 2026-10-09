import ZkFormal.NearV3.Candidates.ProcPriorCodecSideNext
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecNativeBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash

def header (R : Run) : List Nat := [0,(R.n*R.n)%256,(R.n*R.n)/256%256,0,0]
def parameters (I : Input) (R : Run) : List Nat :=
  header R++bytesLE I.p.base 3++bytesLE (I.p.maxShardBandwidth/R.n) 3

def priorHash (I : Input) (present : Bool) : List Nat :=
  if present then I.prev.sanityHash.map UInt8.toNat else List.replicate 32 0

def digest (I : Input) (present : Bool) : List Nat :=
  (NearSpec.sha256 ((priorHash I present++I.ash.map UInt8.toNat).map UInt8.ofNat)).map UInt8.toNat

theorem get_bound (xs : List Nat) (h:∀x∈xs,x<256) (i : Nat) : xs[i]!<256 := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih =>
    cases i with
    | zero => simpa using h a (by simp)
    | succ i =>
      simpa using ih (fun x hx=>h x (by simp [hx])) i

theorem byte_list (xs : List UInt8) (i : Nat) : (xs.map UInt8.toNat)[i]!<256 := by
  apply get_bound
  intro x hx
  obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hx
  exact UInt8.toNat_lt b

theorem header_bound (R : Run) (p : Nat) : (header R)[p]!<256 := by
  apply get_bound
  intro x hx
  simp only [header,List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl
  all_goals first | exact Nat.mod_lt _ (by decide) | decide

theorem digest_bound (I : Input) (present : Bool) (j : Nat) : (digest I present)[j]!<256 :=
  byte_list _ j

theorem header_bytes (I : Input) (R : Run) (present : Bool) (vidV p : Nat)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈ProcPriorCodecSideBytes.byteGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV)
        (parameters I R) (header R) present p)[c]!) nxt first last trans)=0 :=
  ProcPriorCodecSideBytes.header_bytes I R present vidV (parameters I R) (header R) p
    (header_bound R p) nxt first last trans

theorem hash_bytes (I : Input) (R : Run) (present : Bool) (vidV j : Nat)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈ProcPriorCodecSideBytes.byteGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (hashRow (instanceCells I R present vidV)
        (digest I present) (priorHash I present) present (5+24*(R.n*R.n)) j)[c]!) nxt first last trans)=0 :=
  ProcPriorCodecSideBytes.hash_bytes I R present vidV (digest I present) (priorHash I present)
    (5+24*(R.n*R.n)) j (digest_bound I present j) nxt first last trans

end ZkFormal.NearV3.Candidates.ProcPriorCodecNativeBytes
