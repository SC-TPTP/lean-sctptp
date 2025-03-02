import Lean
import Auto.IR.TPTP_TH0
import Auto.IR.TPTP_FOF
import Auto.Parser.TPTP
import Auto.Embedding.LamBase
open Lean

initialize
  registerTraceClass `auto.tptp.result
  registerTraceClass `auto.tptp.printQuery
  registerTraceClass `auto.tptp.printProof
  registerTraceClass `auto.tptp.premiseSelection

register_option auto.tptp : Bool := {
  defValue := false
  descr := "Enable/Disable TPTP"
}

register_option auto.tptp.trust : Bool := {
  defValue := false
  descr :=
    "When this option is set to `true`, auto closes the " ++
    "goal by `autoTPTPSorry` if TPTP solver proves the problem"
}

axiom autoTPTPSorry.{u} (α : Sort u) : α

register_option auto.tptp.premiseSelection : Bool := {
  defValue := true
  descr := "Enable/Disable premise selection by TPTP solvers"
}

register_option auto.tptp.timeout : Nat := {
  defValue := 10
  descr := "Time limit for TPTP solvers (seconds)"
}

namespace Auto

open Parser.TPTP

namespace Solver.TPTP

inductive ZEPortType where
  | fo
  | lams
deriving BEq, Hashable, Inhabited, Repr

inductive SolverName where
  -- Disable TPTP prover
  | zipperposition
  -- zipperposition + E theorem prover, portfolio
  | zeport (zept : ZEPortType)
  -- E prover, higher-order version
  | eproverHo
  | vampire
deriving BEq, Hashable, Inhabited, Repr

instance : ToString SolverName where
  toString : SolverName → String
  | .zipperposition => "zipperposition"
  | .zeport zept =>
    match zept with
    | .fo => "zeport-fo"
    | .lams => "zeport-lams"
  | .eproverHo => "eprover-ho"
  | .vampire => "vampire"

instance : Lean.KVMap.Value SolverName where
  toDataValue n := toString n
  ofDataValue?
  | "zipperposition" => some .zipperposition
  | "zeport-fo" => some (.zeport .fo)
  | "zeport-lams" => some (.zeport .lams)
  | "eprover-ho" => some .eproverHo
  | "vampire" => some .vampire
  | _ => none

end Auto.Solver.TPTP

open Auto.Solver.TPTP in
register_option auto.tptp.solver.name : SolverName := {
  defValue := SolverName.zipperposition
  descr := "Name of the designated TPTP solver"
}

register_option auto.tptp.zipperposition.path : String := {
  defValue := "zipperposition"
  descr := "Path to zipperposition, defaults to \"zipperposition\""
}

register_option auto.tptp.zeport.path : String := {
  defValue := "zeport"
  descr := "Path to the zipperposition-E portfolio"
}

register_option auto.tptp.eproverHo.path : String := {
  defValue := "eprover-ho"
  descr := "Path to higher-order version of E theorem prover"
}

register_option auto.tptp.vampire.path : String := {
  defValue := "vampire"
  descr := "Path to vampire prover"
}

register_option auto.tptp.egg.path : String := {
  defValue := "egg"
  descr := "Path to egg prover"
}

register_option auto.tptp.goeland.path : String := {
  defValue := "goeland"
  descr := "Path to goeland prover"
}

register_option auto.tptp.prover9.path : String := {
  defValue := "p9.jar"
  descr := "Path to Prover9 JAR file"
}

namespace Auto.Solver.TPTP

abbrev SolverProc := IO.Process.Child ⟨.piped, .piped, .piped⟩

private def createAux (path : String) (args : Array String) : MetaM SolverProc :=
    IO.Process.spawn {stdin := .piped, stdout := .piped, stderr := .piped,
                      cmd := path, args := args}

def queryZipperposition (query : String) : MetaM (Bool × String) := do
  let path := auto.tptp.zipperposition.path.get (← getOptions)
  let tlim := auto.tptp.timeout.get (← getOptions)
  let solver ← createAux path #["-i=tptp", "-o=tptp", "--mode=ho-competitive", s!"-t={tlim}"]
  solver.stdin.putStr s!"{query}\n"
  let (_, solver) ← solver.takeStdin
  let stdout ← solver.stdout.readToEnd
  let stderr ← solver.stderr.readToEnd
  trace[auto.tptp.result] "Result: \nstderr:\n{stderr}\nstdout:\n{stdout}"
  solver.kill
  let proven := (stdout.splitOn "SZS status Unsatisfiable").length >= 2
  return (proven, stdout)

def queryZEPort (zept : ZEPortType) (query : String) : MetaM (Bool × String) := do
  let path := auto.tptp.zeport.path.get (← getOptions)
  -- To avoid concurrency issue, use `attempt`
  attempt <| IO.FS.createDir "./.zeport_ignore"
  let mut idx := 0
  -- Synchronization
  while true do
    try
      IO.FS.createDir s!"./.zeport_ignore/tmp{idx}"
      break
    catch e =>
      let estr := toString (← (Exception.toMessageData e).format)
      if estr.extract ⟨0⟩ ⟨44⟩ != "already exists (error code: 17, file exists)" then
        throwError "{decl_name%} :: Unexpected error"
      idx := idx + (← IO.rand 0 100)
  IO.FS.withFile s!"./.zeport_ignore/problem{idx}.p" .writeNew (fun stream => stream.putStr query)
  let solver ← createSolver path idx
  let stdout ← solver.stdout.readToEnd
  let stderr ← solver.stderr.readToEnd
  trace[auto.tptp.result] "Result: \nstderr:\n{stderr}\nstdout:\n{stdout}"
  solver.kill
  IO.FS.removeFile s!"./.zeport_ignore/problem{idx}.p"
  -- For synchronization, remove directory in the end
  IO.FS.removeDirAll s!"./.zeport_ignore/tmp{idx}"
  let proven := (stdout.splitOn "SZS status Unsatisfiable").length >= 2
  return (proven, stdout)
where
  attempt (action : MetaM Unit) : MetaM Unit := try action catch _ => pure ()
  createSolver (path : String) (idx : Nat) := do
    let path := if ("A" ++ path).back == '/' then path else path ++ "/"
    let tlim := auto.tptp.timeout.get (← getOptions)
    match zept with
    | .fo => createAux "python3" #[path ++ "portfolio.fo.parallel.py", s!"./.zeport_ignore/problem{idx}.p", s!"{tlim}", "true"]
    | .lams => createAux "python3" #[path ++ "portfolio.lams.parallel.py", s!"./.zeport_ignore/problem{idx}.p", s!"{tlim}", s!"./.zeport_ignore/tmp{idx}", "true"]

def queryE (query : String) : MetaM (Bool × String) := do
  let path := auto.tptp.eproverHo.path.get (← getOptions)
  let tlim := auto.tptp.timeout.get (← getOptions)
  let solver ← createAux path #["--tstp-format", s!"--cpu-limit={tlim}"]
  solver.stdin.putStr s!"{query}\n"
  let (_, solver) ← solver.takeStdin
  let stdout ← solver.stdout.readToEnd
  let stderr ← solver.stderr.readToEnd
  trace[auto.tptp.result] "Result: \nstderr:\n{stderr}\nstdout:\n{stdout}"
  solver.kill
  let proven := (stdout.splitOn "Proof found!").length >= 2
  return (proven, stdout)

def queryVampire (query : String) : MetaM (Bool × String) := do
  let path := auto.tptp.vampire.path.get (← getOptions)
  let tlim := auto.tptp.timeout.get (← getOptions)
  let solver ← createAux path #["--mode", "casc", "--time_limit", s!"{tlim}"]
  solver.stdin.putStr s!"{query}\n"
  let (_, solver) ← solver.takeStdin
  let stdout ← solver.stdout.readToEnd
  let stderr ← solver.stderr.readToEnd
  trace[auto.tptp.result] "Result: \nstderr:\n{stderr}\nstdout:\n{stdout}"
  solver.kill
  let proven := (stdout.splitOn "Refutation found. Thanks to Tanya!").length >= 2
  return (proven, stdout)

def querySolver (query : String) : MetaM (Bool × Array Parser.TPTP.Command) := do
  if !(auto.tptp.get (← getOptions)) then
    throwError "{decl_name%} :: Unexpected error"
  let (proven, stdout) ← (do
    match auto.tptp.solver.name.get (← getOptions) with
    | .zipperposition => queryZipperposition query
    | .zeport zept    => queryZEPort zept query
    | .eproverHo      => queryE query
    | .vampire        => queryVampire query)
  return (proven, ← Parser.TPTP.parse stdout)


/-- Helper function for executing file-based TPTP solvers -/
def queryFileBasedSolver (solverName : String) (executable : String)
  (buildArgs : String → String → Array String)
  (isProvenFn : String → String → String → Bool)
  (query : String) : MetaM (Option (Array Parser.TPTP.Command)) := do
  -- Hash the query to create unique file names
  let queryHash := toString <| hash query
  let problemFile := s!"./tmp/.{solverName}_problem_{queryHash}.p"
  let solutionFile := s!"./tmp/.{solverName}_solution_{queryHash}.p"

  -- Create input and output files
  IO.FS.withFile problemFile .writeNew (fun stream => stream.putStr (query ++ "\n"))
  IO.FS.withFile solutionFile .writeNew (fun stream => stream.putStr "")

  -- Execute solver
  let solver ← createAux executable (buildArgs problemFile solutionFile)
  let stdout ← solver.stdout.readToEnd
  let stderr ← solver.stderr.readToEnd
  solver.kill

  -- Read proof from solution file
  let proof ← IO.FS.readFile solutionFile
  let proven := isProvenFn stdout stderr proof

  -- Clean up temporary files
  IO.FS.removeFile problemFile
  IO.FS.removeFile solutionFile

  -- Log results
  if proven then
    trace[auto.tptp.result] "Proof: \n{proof}"
    return some (← Parser.TPTP.parse proof)
  else
    trace[auto.tptp.result] "Result: \nstderr:\n{stderr}\nstdout:\n{stdout}\nproof:\n{proof}"
    return none

def queryEggSolver (query : String) : MetaM (Option (Array Parser.TPTP.Command)) := do
  let executable := auto.tptp.egg.path.get (← getOptions)
  queryFileBasedSolver "egg" executable
    (fun problemFile solutionFile => #["--level1", problemFile, solutionFile])
    (fun stdout stderr _ => stdout == "" ∧ stderr == "")
    query

def queryGoelandSolver (query : String) : MetaM (Option (Array Parser.TPTP.Command)) := do
  let executable := auto.tptp.goeland.path.get (← getOptions)
  queryFileBasedSolver "goeland" executable
    (fun problemFile solutionFile =>
      #["-otptp", "-wlogs", "-no_id", "-quoted_pred",
        s!"-proof_file={solutionFile.dropRight 2}", problemFile])
    (fun _ stderr proof => stderr == "" ∧ proof != "")
    query


def containsSubstr (s : String) (sub : String) : Bool :=
  if sub.isEmpty then true
  else
    let endIdx := s.endPos.byteIdx - sub.endPos.byteIdx + 1
    let rec checkFrom (i : Nat) : Bool :=
      if i < endIdx then
        if s.substrEq ⟨i⟩ sub 0 sub.endPos.byteIdx then true
        else checkFrom (i + 1)
      else false
    termination_by endIdx - i
    checkFrom 0

def queryProver9Solver (query : String) : MetaM (Option (Array Parser.TPTP.Command)) := do
  let executable := "java"
  let jarPath := auto.tptp.prover9.path.get (← getOptions)
  queryFileBasedSolver "prover9" executable
    (fun problemFile solutionFile => #["-jar", jarPath, problemFile, solutionFile])
    (fun _ stderr proof => !(containsSubstr stderr "SEARCH FAILED") ∧ proof != "")
    query

end Solver.TPTP

end Auto
