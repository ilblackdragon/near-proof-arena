import ZkFormal.NearV3.Candidates.ProcPriorRawSlots
import ZkFormal.NearV3.Candidates.ProcPriorRawRows
import ZkFormal.NearV3.Candidates.ProcPriorCells
namespace ZkFormal.NearV3.Candidates.ProcPriorRawGen
open ZkFormal.Air ZkFormal.Algebra NearSpec.Bandwidth
open ProcPriorRawSlots

def isHeader : Slot→Bool | .header _=>true | _=>false
def isRecord : Slot→Bool | .record _ _=>true | _=>false
def isHash : Slot→Bool | .hash _=>true | _=>false
def active : Slot→Bool | .padding=>false | _=>true
def offset : Slot→Nat | .header g | .record _ g | .hash g=>g | .padding=>0
def record (n : Nat) : Slot→Nat | .record j _=>j | .hash _=>n | _=>0
def endAt : Slot→Nat | .header _=>4 | .record _ _=>23 | .hash _=>31 | .padding=>0

def cells (st : State) (vid : Nat) (present : Bool) (pos : Nat) (s : Slot) : Nat→Fp:=
  if s=.padding then fun _=>0 else
  let n:=st.links.length
  let g:=offset s
  let j:=record n s
  let b:=Fp.ofNat ((st.encode.getD pos 0).toNat)
  fun c=>match c with
  | 0=>1
  | 1=>0
  | 2=>Fp.ofNat vid
  | 3=>ProcPriorCells.bit present
  | 4=>Fp.ofNat pos
  | 5=>b
  | 6=>ProcPriorCells.bit (isHeader s)
  | 7=>ProcPriorCells.bit (isRecord s)
  | 8=>ProcPriorCells.bit (isHash s)
  | 9=>Fp.ofNat g
  | 10=>Fp.ofNat j
  | 11=>Fp.ofNat n
  | 12=>ProcPriorCells.bit (decide (g=endAt s))
  | 13=>(Fp.ofNat g-Fp.ofNat (endAt s))⁻¹
  | 14=>ProcPriorCells.bit (isRecord s && decide (j+1=n))
  | 15=>(Fp.ofNat (j+1)-Fp.ofNat n)⁻¹
  | 16=>ProcPriorCells.bit (decide (n=0))
  | 17=>(Fp.ofNat n)⁻¹
  | 18=>ProcPriorCells.bit (isHeader s && decide (g=0))
  | 19=>if isHeader s then Fp.ofNat (n/256^(g-1)) else 0
  | 20=>ProcPriorCells.bit present
  | 21=>(Fp.ofNat g)⁻¹
  | 22=>ProcPriorCells.bit (isHeader s && decide (g=0) && present)
  | _=>0

def trace (st : State) (vid : Nat) (present : Bool) : Trace Fp:=
  {log:=fun _=>22,cell:=fun _ r=>cells st vid present r (slot st.links.length r)}

theorem padding_cells (st : State) (vid pos : Nat) (present : Bool) :
    cells st vid present pos .padding=fun _=>0 := by simp [cells]

theorem header_slot (st : State) (vid g : Nat) (present : Bool) (hg:g<5) :
    (trace st vid present).cell 0 g=cells st vid present g (.header g) := by
  simp only [trace,ProcPriorRawSlots.header _ _ hg]

theorem record_slot (st : State) (vid j g : Nat) (present : Bool) (hj:j<st.links.length) (hg:g<24) :
    (trace st vid present).cell 0 (5+24*j+g)=cells st vid present (5+24*j+g) (.record j g) := by
  simp only [trace,ProcPriorRawSlots.record _ _ _ hj hg]

theorem hash_slot (st : State) (vid g : Nat) (present : Bool) (hg:g<32) :
    (trace st vid present).cell 0 (5+24*st.links.length+g)=
      cells st vid present (5+24*st.links.length+g) (.hash g) := by
  simp only [trace,ProcPriorRawSlots.hash _ _ hg]

theorem padding_slot (st : State) (vid j : Nat) (present : Bool) (hj:length st.links.length≤j) :
    (trace st vid present).cell 0 j=fun _=>0 := by
  simp only [trace,ProcPriorRawSlots.padding _ _ hj,padding_cells]

end ZkFormal.NearV3.Candidates.ProcPriorRawGen
