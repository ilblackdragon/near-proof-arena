import ZkFormal.NearV3.Assembly.RcptSkeletonByteHead
import ZkFormal.NearV3.Assembly.RoutingFrameBits

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

/-- Ordinary running native burn total and this receipt's burned amount. The
link to native execution and the no-overflow proof are separate gas obligations. -/
structure TokenInput where
  before : Nat
  burnt : Nat

def TokenInput.oldBytes (x : TokenInput) : Bytes := u128 x.before
def TokenInput.newBytes (x : TokenInput) : Bytes := u128 (x.before+x.burnt)
def TokenInput.window (x : TokenInput) (pos slot : Nat) : UInt8 :=
  (x.oldBytes++x.newBytes).getD (pos+slot) 0

theorem token_bytes_lengths (x : TokenInput) : x.oldBytes.length=16 ∧ x.newBytes.length=16 := by
  simp [TokenInput.oldBytes,TokenInput.newBytes,u128,leN]

theorem token_window_shift (x : TokenInput) (pos slot : Nat) :
    x.window (pos+1) slot=x.window pos (slot+1) := by
  simp only [TokenInput.window]
  congr 1
  omega

theorem token_window_start (x : TokenInput) (slot : Nat) (hs : slot<16) :
    x.window 0 slot=x.oldBytes.getD slot 0 := by
  simp only [TokenInput.window,Nat.zero_add]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append]
  simp only [(token_bytes_lengths x).1,if_pos hs]

theorem token_window_finish (x : TokenInput) (slot : Nat) :
    x.window 16 slot=x.newBytes.getD slot 0 := by
  simp only [TokenInput.window]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append]
  have hnot : ¬16+slot<x.oldBytes.length := by rw [(token_bytes_lengths x).1];omega
  rw [if_neg hnot,(token_bytes_lengths x).1]
  have he : 16+slot-16=slot := by omega
  rw [he]

theorem token_window_tail (x : TokenInput) (pos : Nat) :
    x.window (pos+1) 15=x.newBytes.getD pos 0 := by
  rw [token_window_shift]
  unfold TokenInput.window
  have he : pos+16=16+pos := by omega
  rw [he]
  exact token_window_finish x pos

def tokenOf (x : TokenInput) (row : Coord) (slot : Nat) : UInt8 :=
  if row.state<sGP then x.oldBytes.getD slot 0 else
  if row.state=sGP then x.window row.index slot else x.newBytes.getD slot 0

def nextGas (pos : Nat) : Coord := if pos+1<16 then ⟨sGP,pos+1,16⟩ else ⟨sTL,0,13⟩

theorem tokenOf_gas (x : TokenInput) (pos slot : Nat) :
    tokenOf x ⟨sGP,pos,16⟩ slot=x.window pos slot := by simp [tokenOf]

theorem tokenOf_nextGas (x : TokenInput) (pos slot : Nat) (hp : pos<16) :
    tokenOf x (nextGas pos) slot=x.window (pos+1) slot := by
  unfold nextGas
  split
  · exact tokenOf_gas _ _ _
  · rename_i hn
    have he : pos+1=16 := by omega
    rw [he,token_window_finish]
    rfl

theorem tokenOf_gas_shift (x : TokenInput) (pos slot : Nat) (hp : pos<16) :
    tokenOf x (nextGas pos) slot=tokenOf x ⟨sGP,pos,16⟩ (slot+1) := by
  rw [tokenOf_nextGas _ _ _ hp,tokenOf_gas,token_window_shift]

theorem tokenOf_gas_tail (x : TokenInput) (pos : Nat) (hp : pos<16) :
    tokenOf x (nextGas pos) 15=x.newBytes.getD pos 0 := by
  rw [tokenOf_nextGas _ _ _ hp,token_window_tail]

end ZkFormal.NearV3.Assembly.RcptSkeleton
