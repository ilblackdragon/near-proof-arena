import ZkFormal.NearV3.Qv.Candidates.RawRender
import ZkFormal.NearV3.Qv.Candidates.BufferRender
import ZkFormal.NearV3.Qv.Candidates.EmptyPaddedRender
import ZkFormal.NearV3.Qv.Candidates.RecordGlue

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air

inductive Payload where
  | empty (index : Bytes)
  | buffer (entries : List ByteBuffer)
  | raw (bytes : Bytes)

structure Record where
  vid : Nat
  tau : Nat
  users : Nat
  payload : Payload

def Record.Valid (v : Record) : Prop :=
  match v.payload with
  | .empty index => index.length=8
  | .buffer es => (∀ e ∈ es, e.Sized) ∧ es.length<16777216
  | .raw _ => True

def Record.rows (v : Record) : List (List Nat) :=
  match v.payload with
  | .empty index => emptyRows v.vid v.tau v.users index
  | .buffer es => bufferRows v.vid v.tau v.users es
  | .raw bytes => rawRows v.vid v.tau v.users bytes

def Record.size (v : Record) : Nat :=
  match v.payload with
  | .empty _ => 16
  | .buffer es => 4+24*es.length
  | .raw bytes => max 1 bytes.length

theorem Record.size_pos (v : Record) : 0<v.size := by
  cases v with | mk vid tau users p => cases p <;> simp [Record.size] <;> omega

theorem Record.rows_length (v : Record) (hv : v.Valid) : v.rows.length=v.size := by
  cases v with
  | mk vid tau users p =>
    cases p with
    | empty index => simp [Record.rows,Record.size,emptyRows,Record.Valid] at hv ⊢; omega
    | buffer es => exact bufferRows_length vid tau users es hv.1
    | raw bytes =>
      by_cases h : bytes=[]
      · simp [Record.rows,Record.size,rawRows,h]
      · have hp : 0<bytes.length := List.length_pos_iff.mpr h
        simp [Record.rows,Record.size,rawRows,List.isEmpty_eq_false_iff.mpr h,Nat.max_eq_right hp]

variable {F : Type} [Lean.Grind.CommRing F]

def Record.trace (v : Record) (log : Nat) : Trace F :=
  { log := fun _ => log,
    cell := fun _ r c => @Nat.cast F Lean.Grind.Semiring.natCast
      ((v.rows.getD r []).getD c 0) }

theorem Record.local (v : Record) (hv : v.Valid) (log : Nat)
    (hb : v.size≤2^log) {r : Nat} (hr : r<2^log) :
    ∀ e ∈ ValueTable.table.allConstraints, e.eval (v.trace (F:=F) log) 0 r []=0 := by
  cases v with
  | mk vid tau users p =>
    cases p with
    | empty index => exact emptyGeneratedPaddedTrace_local log vid tau users index hv hb hr
    | buffer es => exact bufferGeneratedTrace_local log vid tau users es hv.1 hv.2 hb hr
    | raw bytes =>
      exact rawGeneratedTrace_local log vid tau users bytes
        (Nat.le_trans (Nat.le_max_right 1 bytes.length) hb) hr

end ZkFormal.NearV3.Qv.Candidates.ValueGen
