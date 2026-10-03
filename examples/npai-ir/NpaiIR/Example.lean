import NpaiIR.Correct

/-! A tiny compiled program: accept iff the claim is non-empty, computing its
length with a loop (exercises `loop`, `ite`, `seq`, `halt`). -/

namespace NpaiIR.Example

open ArenaCore Interp

def prog : Stmt :=
  .seq (.op (.tlen 1 .claim))
  (.seq (.op (.const 2 0))
  (.seq (.op (.const 3 1))
  (.seq (.loop 1 (.seq (.op (.bin .sub 1 1 3)) (.op (.bin .add 2 2 3))))
  (.ite 2 (.halt 3) (.halt 1)))))

def program : Program := { memSize := 0, data := [], code := prog.compile 0 }

example : interpVerify (encode program) 1000 [] [7, 8, 9] [] = true := by decide +kernel
example : interpVerify (encode program) 1000 [] [] [] = false := by decide +kernel
/-- Fuel exhaustion inside the loop is rejection. -/
example : interpVerify (encode program) 5 [] [7, 8, 9] [] = false := by decide +kernel

theorem prog_wf : prog.wf := by simp [prog, Stmt.wf, plain]

end NpaiIR.Example
