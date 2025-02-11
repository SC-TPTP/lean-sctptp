import Auto.IR.TPTP_FOF
import Auto.Translation.LamUtils

namespace Auto
open Lean Embedding.Lam Lam2FOF

def lam2FOF (lamVarTy : Array LamSort) (lamEVarTy : Array LamSort) (facts : Array LamTerm) : CoreM String := do
  if (lamVarTy ++ lamEVarTy).any (fun s => s == .base .empty) then
    return "fof(empty_inhabited, axiom, $false)."
  let nFacts := facts.size
  let factsStrs ← facts.zipWithIndex.mapM (fun (t, i) =>
    if i == nFacts - 1 then
      match t with
      | .app _ (.base (.pcst .not)) t =>
        match transLamTerm t with
        | .ok ts => return s!"fof(c, conjecture, {ts})."
        | .error e => throwError e
      | _ => throwError "lam2FOF :: unexpected error"
    else
      match transLamTerm t with
      | .ok ts =>
        return s!"fof(a{i}, axiom, {ts})."
      | .error e => throwError e)
  return String.intercalate "\n" factsStrs.toList

end Auto
