import ReexecNpai.Prog.Front
import ReexecNpai.Prog.Final
import NpaiIR.Encode

/-!
# The verifier program and its bytecode image

`code = encode program` is the shipped `verifier.npai` (`build.sh` writes it
with the exporter `Export.lean`); its SHA-256 is the `bytecodeDigest` of the
admission statement.
-/

namespace ReexecNpai

open NpaiIR ArenaCore Interp

def body : Stmt := seqs [pSetup, pClaim, pProof, pReceipts, pParse, pHash, pRootIs (CLM + 117),
  pBatch, pFinal]

def prog : Stmt := .seq body (.halt 15)

def program : Program := { memSize := MEMSIZE, data := dataSeg, code := prog.compile 0 }

def code : Bytes := encode program

end ReexecNpai
