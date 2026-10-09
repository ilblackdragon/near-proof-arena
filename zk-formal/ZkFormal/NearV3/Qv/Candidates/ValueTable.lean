import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Rcpt.Ids

/-! Candidate queue value parser, not part of admitted/concrete AIR yet.
One row per authenticated byte; raw zero-length values use one marker row.
Modes: empty indices, buffered indices, uninterpreted raw value. Buffered
shard bytes are emitted separately, avoiding u64 field reduction. This candidate
uses QSH(tau,entry,byte-position,byte), with position8 reserved for vector count;
the old unused QSH vector schema must be replaced coherently in final assembly.
Sound extraction, honest rendering, queue walks and row bounds remain required.
-/
namespace ZkFormal.NearV3.Qv.Candidates.ValueTable
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

def B_QVC : Nat := 63

def act := 0
def vf := 1
def vl := 2
def vid := 3
def len := 4
def pos := 5
def byte := 6
def users := 7
def tau := 8
def entry := 9
def count := 10
def vz := 11
def gb := 12
def cont := 13
def mEmpty := 14
def mBuffer := 15
def mRaw := 16
def header := 17
def shard := 18
def firstIndex := 19
def nextIndex := 20
def sel (i : Nat) := 21+i
def reg (i : Nat) := 29+i
def width := 37

def modes := [mEmpty,mBuffer,mRaw]
def phases := [header,shard,firstIndex,nextIndex,mRaw]
def selectors := (List.range 8).map sel

def subpos : Expr := sum ((List.range 8).map fun i => smul i (c (sel i)))
def wordEnd : Expr := c (sel 7)
def headerEnd : Expr := .mul (c header) (c (sel 3))
def entryEnd : Expr := .mul (c nextIndex) wordEnd
def mode : Expr := .add (c mBuffer) (smul 2 (c mRaw))
def counterBytes : Expr := sum ((List.range 4).map fun i => smul (256^i) (c (reg i)))
def same (x : Nat) : Expr := eqG (c cont) (n x) (c x)

def constraints : List Expr :=
  ([act,vf,vl,vz,gb,cont] ++ modes ++ [header,shard,firstIndex,nextIndex] ++ selectors).map
    (fun x => bool (c x)) ++
  [ sub (sum (modes.map c)) (c act),
    sub (sum (phases.map c)) (c act),
    sub (sum (selectors.map c)) (sub (c act) (c mRaw)),
    sub (c cont) (.mul (c act) (not (c vl))),
    sub (c gb) (sub (c act) (c vz)),
    .mul (c vf) (not (c act)), .mul (c vl) (not (c act)),
    .mul (c vz) (not (c mRaw)),
    .mul (c vz) (not (c vf)), .mul (c vz) (not (c vl)),
    .mul (c vz) (c len), .mul (c vz) (c byte),
    .mul (c header) (not (c mBuffer)), .mul (c shard) (not (c mBuffer)),
    -- First row, padding and segment boundaries.
    .mul .isFirst (sub (c act) (c vf)),
    mul3 .isLast (c act) (not (c vl)),
    mul3 .isTransition (not (c act)) (n act),
    mul3 .isTransition (c vl) (.mul (n act) (not (n vf))),
    .mul (c cont) (not (n act)), .mul (c cont) (n vf),
    .mul (c vf) (c pos), .mul (c vf) (c entry),
    eqG (c vf) (c header) (c mBuffer),
    eqG (c vf) (c firstIndex) (c mEmpty),
    eqG (c vf) (c (sel 0)) (not (c mRaw)),
    eqG (c cont) (n pos) (.add (c pos) (k 1)),
    mul3 (c vl) (not (c vz)) (sub (c len) (.add (c pos) (k 1))),
    -- Endpoints: empty indices have exactly two eight-byte words.
    eqG (c mEmpty) (c vl) entryEnd,
    mul3 (c vl) (c header) (not (c (sel 3))),
    mul3 (c vl) (c nextIndex) (not wordEnd),
    mul3 (c vl) (c mBuffer) (sub (.add (c header) (c nextIndex)) (k 1)),
    mul3 (c vl) (c header) (c count),
    mul3 (c vl) (c nextIndex) (.mul (c mBuffer)
      (sub (.add (c entry) (k 1)) (c count))),
    -- Header count has at most three significant bytes. Assembly derives this
    -- from the authenticated byte budget; this is not a new accepted-domain cap.
    .mul (c header) (c (reg 3)),
    eqG headerEnd (c count) counterBytes,
    -- Clock reset at header byte3 and all other word byte7.
    eqG (c cont) (n (sel 0)) (.add wordEnd headerEnd),
    eqG (c cont) (n entry) (.add (c entry) entryEnd),
    -- Phase machine. A completed last-index word either ends the record or
    -- starts the next buffered entry. Empty-mode completion must end the record.
    eqG (c cont) (n header) (.mul (c header) (not (c (sel 3)))),
    eqG (c cont) (n shard) (sum [.mul (c shard) (not wordEnd),headerEnd,entryEnd]),
    eqG (c cont) (n firstIndex)
      (.add (.mul (c firstIndex) (not wordEnd)) (.mul (c shard) wordEnd)),
    eqG (c cont) (n nextIndex)
      (.add (.mul (c nextIndex) (not wordEnd)) (.mul (c firstIndex) wordEnd)) ] ++
  [vid,len,users,tau,count,mEmpty,mBuffer,mRaw].map same ++
  (List.range 4).map (fun i => .mul (c header) (c (sel (i+4)))) ++
  (List.range 7).map (fun i =>
    eqG (c cont) (n (sel (i+1)))
      (if i=3 then .mul (c (sel i)) (not (c header)) else c (sel i))) ++
  (List.range 8).map (fun i =>
    mul3 (c (sel i)) (sum [c header,c firstIndex,c nextIndex])
      (sub (c byte) (c (reg i)))) ++
  (List.range 8).map (fun i =>
    mul3 (c cont) (not (.add headerEnd entryEnd)) (sub (n (reg i)) (c (reg i))))

def interactions : List Interaction :=
  [ send B_VBYTES (c gb) [c vid,c pos,c byte],
    send B_QVC (c vf) [c vid,c tau,mode,k 0],
    recv B_QVC (c vf) [c vid,c tau,mode,c users],
    send B_QSH (c shard) [c tau,c entry,subpos,c byte],
    send B_QSH headerEnd [c tau,k 0,k 8,c count] ]

/-- Provisional shape only; actual capacity must be derived from value records
and their zero-length markers, without the obsolete 128KiB queue restriction. -/
def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := 22 }

end ZkFormal.NearV3.Qv.Candidates.ValueTable
