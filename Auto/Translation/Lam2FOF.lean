import Auto.IR.TPTP_FOF
import Auto.Translation.LamUtils

namespace Auto
open Lean Embedding.Lam Lam2FOF

def lam2FOF (lamVarTy : Array LamSort) (lamEVarTy : Array LamSort) (facts : Array LamTerm) : CoreM String := do
  if (lamVarTy ++ lamEVarTy).any (fun s => s == .base .empty) then
    return "fof(empty_inhabited, axiom, $false)."
  let facts ← facts.zipWithIndex.mapM (fun (t, i) =>
    match transLamTerm t with
    | .ok ts => return s!"fof(fact{i}, axiom, {ts})."
    | .error e => throwError e)
  let sep := "\n"
  return String.intercalate sep facts.toList

end Auto
