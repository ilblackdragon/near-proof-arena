import NearCompression.PreparedMemoryStoreService
import NearCompression.CachedWriteBytes
import NearCompression.SHA384Chain
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm
private def hash (bs : Bytes) : ByteArray := ⟨(sha384ChainDigest bs).toArray⟩
private def ensure (ok : Bool) (why : String) : IO Unit := unless ok do throw (IO.userError why)
private def initial : St := {
  pages:=#[zeroPage],globals:=#[],table:=#[],tableMax:=0,
  elems:=#[],datas:=#[],stackRem:=262144,gas:=Gas.init 0}
private def request (s : St) (clock value : Nat) : PreparedMemoryStoreRequest :=
  {clock,address:=17,width:=1,value,
   batches:=cachedWriteBytesWitness hash s 4096 16 4 17 ⟨#[UInt8.ofNat value]⟩}
end NearCompression
open NearCompression NearSpecV3.Wasm

def main : IO Unit := do
  let s:=initial
  let first:=request s 11 5
  let afterFirst:=writeLE s 17 1 5
  let second:=request afterFirst 12 9
  let final:=writeLE afterFirst 17 1 9
  let root:=describeSubpageMemory hash s 4096 16 4
  let run:=preparedMemoryStoreServiceCheck hash root 11
  ensure (run [] == some root) "empty sequence"
  ensure (run [first,second] == some (describeSubpageMemory hash final 4096 16 4)) "honest ordered overwrite"
  ensure ((run [second,first]).isNone) "reordered clocks"
  ensure ((run [first,first]).isNone) "repeated clock"
  ensure ((run [first,{second with clock:=13}]).isNone) "skipped clock"
  ensure ((run [{first with clock:=10},second]).isNone) "wrong initial clock"
  ensure ((run [first,request s 12 9]).isNone) "stale second root/opening"
  ensure ((run [first,{second with address:=18}]).isNone) "request address detached from batches"
  ensure ((run [first,{second with value:=10}]).isNone) "request value detached from batches"
  ensure ((run [first,{second with width:=2}]).isNone) "request width detached from batches"
  IO.println "memory service PASS: empty + two ordered overwrites; eight chronology/root/request forgeries rejected"
