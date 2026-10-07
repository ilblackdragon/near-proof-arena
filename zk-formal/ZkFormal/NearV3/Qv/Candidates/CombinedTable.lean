import ZkFormal.NearV3.Qv.Candidates.ValueTable
import ZkFormal.Size.Model

/-! Executable combined read/parser candidate, not admitted. Walk rows precede
parser records and reuse raw-empty marker rows. The parser length cell holds the
read mode on walk rows; virtualizing it to zero preserves the marker equations.
Global extraction, honest rendering and native capacity remain obligations. -/
namespace ZkFormal.NearV3.Qv.Candidates.CombinedTable
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl
open ValueTable

def walk := 37
def lo := 38
def hi := 39
def wp := 40
def wb := 41
def slot := 42
def wf := 43
def wl := 44
def wend := 45
def absent := 46
def groupByte := 47
def countRead := 48
def main := 49
def lastMain := 50
def present := 51
def width := 52

/-- Only the unused raw-empty length cell is overlaid. -/
def parserExpr : Expr → Expr
  | .col x next => if x = len then .mul (.col x next) (not (.col walk next)) else .col x next
  | .add a b => .add (parserExpr a) (parserExpr b)
  | .mul a b => .mul (parserExpr a) (parserExpr b)
  | .neg a => .neg (parserExpr a)
  | e => e

def group : Expr := .mul (c lo) (c hi)
def inside : Expr := .mul (c walk) (not (c wl))
def more : Expr := sub (c wl) (c wend)
def advanceMain : Expr := mul3 more (c main) (not (c lastMain))
def leaveMain : Expr := .mul more (c lastMain)
def advanceImplicit : Expr := .mul more (not (c main))
def wid : Expr := sum [k W_QV,c tau,smul 64 (c slot)]
def kPublic : Expr := sum ((List.range 4).map fun i => smul (256^i) (.pub (26+i)))
def readMode : Expr := c len
def nibble (start : Nat) : Expr :=
  sum ((List.range 4).map fun i => smul (2^i) (c (reg (start+i))))

def constraints : List Expr := ValueTable.constraints.map parserExpr ++
  [walk,lo,hi,wf,wl,wend,absent,groupByte,countRead,main,lastMain,present].map
    (fun x => bool (c x)) ++
  [wf,wl,wend,groupByte,countRead,main,lastMain,present].map
    (fun x => .mul (c x) (not (c walk))) ++
  (List.range 8).map (fun i => .mul (c walk) (bool (c (reg i)))) ++
  [ eqG (c walk) (c act) (k 1), eqG (c walk) (c vz) (k 1),
    eqG (c walk) (c mRaw) (k 1),
    eqG (c walk) (c wb) (.add (nibble 0) (smul 16 (nibble 4))),
    eqG (c walk) readMode
      (.add (.mul (c main) (.add (c lo) group)) (smul 2 (not (c main)))),
    .mul (c wend) (not (c wl)), .mul (c lastMain) (not (c main)),
    .mul (c lastMain) (not (c hi)), .mul (c absent) (.mul (c walk) (c vid)),
    sub (c present) (.mul (c wl) (not (c absent))),
    sub (c groupByte) (mul3 (c walk) group (not (c wf))),
    sub (c countRead) (mul3 (c present) (c main) (.mul (c lo) (not (c hi)))),
    .mul (c wf) (c wp), eqG (c wl) (c wp) (smul 8 group),
    eqG (c wf) (c wb) (sum [k 7,smul 6 (c lo),smul 3 (c hi)]),
    .mul .isFirst (not (c walk)), .mul .isFirst (not (c wf)),
    .mul .isFirst (not (c main)), .mul .isFirst (c tau),
    .mul .isFirst (c slot), .mul .isFirst (c lo), .mul .isFirst (c hi),
    mul3 .isLast (c walk) (not (c wend)),
    mul3 .isTransition (not (c walk)) (n walk),
    eqG inside (n walk) (k 1), .mul inside (n wf),
    eqG inside (n wp) (.add (c wp) (k 1)),
    eqG more (n walk) (k 1), eqG more (n wf) (k 1),
    mul3 .isTransition (c wend) (n walk),
    eqG (c wend) (c tau) kPublic,
    mul3 (c wend) (c main) (not (c lastMain)),
    .mul (c main) (c tau),
    mul3 (c walk) (not (c main)) (c lo),
    mul3 (c walk) (not (c main)) (c hi),
    mul3 (c walk) (not (c main)) (c slot),
    eqG (c lastMain) (c count) (.mul (c lo) (sub (c slot) (k 2))),
    mul3 (c wl) (.mul (c main) (.mul (c lo) (not (c hi)))) (.mul (c absent) (c count)),
    eqG advanceMain (n main) (k 1),
    eqG advanceMain (n slot) (.add (c slot) (k 1)),
    eqG advanceMain (n lo) (not (.mul (c lo) (not (c hi)))),
    eqG advanceMain (n hi) (sub (.add (c lo) (c hi)) group),
    eqG advanceMain (n count) (c count),
    eqG leaveMain (n main) (k 0), eqG leaveMain (n tau) (k 1),
    eqG advanceImplicit (n main) (k 0),
    eqG advanceImplicit (n tau) (.add (c tau) (k 1)) ] ++
  [lo,hi,slot,vid,tau,users,absent,main,lastMain,count].map
    (fun x => eqG inside (n x) (c x))

/-- Ordering keeps each degree-three factor paired with a degree-two factor. -/
def interactions : List Interaction :=
  [ send B_VBYTES (c gb) [c vid,c pos,c byte],
    send B_QVC (.mul (c vf) (not (c walk))) [c vid,c tau,mode,k 0],
    recv B_QVC (.mul (c vf) (not (c walk))) [c vid,c tau,mode,c users],
    send B_QSH (c shard) [c tau,c entry,subpos,c byte],
    send B_QSH headerEnd [c tau,k 0,k 8,c count],
    send B_KEYNIB (c wf) [wid,k 0,k SYM_START,k 0],
    send B_KEYNIB (c walk) [wid,.add (smul 2 (c wp)) (k 1),nibble 4,k 0],
    send B_KEYNIB (c walk) [wid,.add (smul 2 (c wp)) (k 2),nibble 0,k 0],
    send B_KEYNIB (c wl) [wid,.add (smul 2 (c wp)) (k 3),k SYM_END,k 1],
    recv B_FINAL (c wl) [wid,c tau,c absent,c vid],
    recv B_QVC (c present) [c vid,c tau,readMode,c users],
    send B_QVC (c present) [c vid,c tau,readMode,.add (c users) (k 1)],
    recv B_QSH (c groupByte) [c tau,sub (c slot) (k 3),sub (c wp) (k 1),c wb],
    recv B_QSH (c countRead) [c tau,k 0,k 8,c count] ]

def table : Air.Table :=
  { width, constraints, interactions, maxLog := 22 }

theorem shape_g2 : ZkFormal.Size.shapeOf 2 table = ⟨52,8,6,8,22⟩ := by decide +kernel
theorem table_wf : table.wf ⟨[table],64,30⟩ 6 = true := by decide +kernel

end ZkFormal.NearV3.Qv.Candidates.CombinedTable
