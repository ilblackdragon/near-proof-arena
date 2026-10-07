import ZkFormal.NearV3.Render.Ups.TreeWrapDispatch

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Metadata at a split terminal before optional wrapper/ancestor parts. -/
def splitInstance (base : UpsInst) (source : PTrie) (key : List Nat) (cs : UCase) (n : Nat)
    (v : Bytes) : UpsInst := traceInstance base (terminalRun source key cs n source []) v

theorem splitInstance_bounds (base : UpsInst) (source : PTrie) (key : List Nat) (cs : UCase)
    (n : Nat) (v : Bytes) (hw : source.wf=true) (hk : FixedSuffix key) (hn : n≤key.length) :
    1≤(splitInstance base source key cs n v).ts ∧ (splitInstance base source key cs n v).ts≤3 ∧
    (splitInstance base source key cs n v).x<16 := by
  have hb := hk.cursor hn
  refine ⟨hb.1,hb.2,?_⟩
  exact splitNibble_lt (run:=terminalRun source key cs n source []) hw

theorem splitInstance_fresh (base : UpsInst) (source : PTrie) (key : List Nat) (cs : UCase)
    (n : Nat) (v : Bytes) (hk : FixedSuffix key) :
    key.drop (n+1)=[0,15].drop (splitInstance base source key cs n v).ts := hk.fresh n

theorem splitInstance_prefix (base : UpsInst) (source : PTrie) (key : List Nat) (cs : UCase)
    (n : Nat) (v : Bytes) (hk : FixedSuffix key) :
    key.take n=([0,15].drop ((splitInstance base source key cs n v).ts-1-
      (splitInstance base source key cs n v).ti)).take (splitInstance base source key cs n v).ti := hk.prefix n

theorem splitInstance_next (base : UpsInst) (source : PTrie) (key : List Nat) (cs : UCase)
    (n : Nat) (v : Bytes) (hk : FixedSuffix key) (y : Nat) (ys : List Nat) (hd : key.drop n=y::ys) :
    y=splitNewSlot (splitInstance base source key cs n v) := hk.next hd

theorem drop_successor_of_cons (key : List Nat) (n x : Nat) (xs : List Nat)
    (hd : key.drop n=x::xs) : key.drop (n+1)=xs := by
  have h := congrArg (List.drop 1) hd
  simpa [List.drop_drop,Nat.add_comm] using h

theorem getD_of_drop_cons (key : List Nat) (n x : Nat) (xs : List Nat)
    (hd : key.drop n=x::xs) : key.getD n 0=x := by
  have h := congrArg (fun l : List Nat => l.getD 0 0) hd
  simpa [List.getD_eq_getElem?_getD,List.getElem?_drop] using h
end ZkFormal.NearV3.Render.UpsGen
