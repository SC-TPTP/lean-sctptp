import Auto.Embedding.LamConv

namespace Auto.Lam2FOF
open Embedding.Lam


def transPropConst : PropConst → String
| .trueE      => "$true"
| .falseE     => "$false"
| .not        => "(~)"
| .and        => "(&)"
| .or         => "(|)"
| .imp        => "(=>)"
| .iff        => "(<=>)"

def transBoolConst : BoolConst → String
| .ofProp     => "(identity)"
| .trueb      => "$true"
| .falseb     => "$false"
| .notb       => "(~)"
| .andb       => "(&)"
| .orb        => "(|)"

def transNatConst (nc : NatConst) : String := "t_" ++ nc.reprAux.replace " " "_"

def transIntConst (ic : IntConst) : String := "t_" ++ ic.reprAux

def transString (s : String) : String :=
  String.join (s.data.map (fun c => s!"d{c.toNat}"))

def transStringConst : StringConst → String
| .strVal s  => "t_strVal_" ++ transString s
| sc         => "t_" ++ sc.reprAux

def transBitVecConst (bvc : BitVecConst) : String := "t_" ++ bvc.reprAux.replace " " "_"

def transLamBaseTerm : LamBaseTerm → Except String String
| .pcst pc    => .ok (transPropConst pc)
| .bcst bc    => .ok (transBoolConst bc)
| .ncst nc    => .ok (transNatConst nc)
| .icst ic    => .ok (transIntConst ic)
| .scst sc    => .ok (transStringConst sc)
| .bvcst bvc  => .ok (transBitVecConst bvc)
| .ocst _     => .error "transLamBaseTerm :: attributes not supported in TPTP"
| .eqI _      => .error "transLamBaseTerm :: eqI should not occur here"
| .forallEI _ => .error "transLamBaseTerm :: forallEI should not occur here"
| .existEI _  => .error "transLamBaseTerm :: existEI should not occur here"
| .iteI _     => .error "transLamBaseTerm :: iteI should not occur here"
| .eq _       => .ok "(=)"
| .forallE _  =>
    .ok "($true)"  -- if the bound sort is empty, we output $true
| .existE _   =>
    .ok "($false)" -- similarly for exists
| .ite _      => .ok "($ite)"  -- treat ite op abstractly

partial def transLamTerm (t : LamTerm) (lctx := 0) : Except String String :=
  match t with
  | .atom n      => .ok s!"t_a{n}"
  | .etom n      => .ok s!"t_e{n}"
  | .base b      => transLamBaseTerm b
  | .bvar n      => .ok s!"X{lctx - n - 1}"
  | .lam _ _     => .error "transLamTerm :: unexpected lambda abstraction encountered in FOF translation"
  | .app _ t₁ t₂ =>
    if t₁.isForallE || t₁.isExistE then
      transQuantApp t₁ t₂ lctx
    else
      match transLamTerm t₁ lctx, transLamTerm t₂ lctx with
      | .ok t₁s, .ok t₂s => .ok s!"({t₁s} @ {t₂s})"
      | .error e, _ => .error e
      | .ok _, .error e => .error e
where
  expandQuantBody (s : LamSort) (t : LamTerm) : LamTerm :=
    match t with
    | .lam _ body => body
    | _ => (LamTerm.app s t (.bvar 0)).headBeta
  transQuantApp (quant body : LamTerm) (lctx : Nat) : Except String String :=
    let info : Except String (String × LamSort) :=
      match quant with
      | .base (.forallE s) => .ok ("!", s)
      | .base (.existE s) => .ok ("?", s)
      | _ => .error "transLamTerm :: Unexpected error"
    match info with
    | .ok (qs, s) =>
      if s == .base .empty then
        match quant with
        | .base (.forallE _) => .ok "$true"
        | .base (.existE _) => .ok "$false"
        | _ => .error "transLamTerm :: Unexpected error"
      else
        match transLamTerm (expandQuantBody s body) (lctx + 1) with
        | .ok bs => .ok s!"({qs} [X{lctx}] : {bs})"
        | .error e => .error e
    | .error e => .error e

end Auto.Lam2FOF
