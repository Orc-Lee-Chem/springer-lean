import SpringerLean.Round402EncodedGramDataCore
import Lean

/- This elaborator returns DATA TERMS ONLY. It does not produce a proof,
assert a Boolean result, add an axiom, or bypass declaration type checking.
Every mathematical property is proved later by the unchanged kernel checker. -/
namespace SpringerLean.GramWitnessQuotation
open Lean

def coefficientType : Lean.Expr :=
  mkApp (mkConst ``RatPolyCheck.Expr [Level.zero]) (toTypeExpr (Bool × Nat))

def quoteCoefficient : CoeffExpr → Lean.Expr
  | .const q => mkApp2 (mkConst ``RatPolyCheck.Expr.const [Level.zero])
      (toTypeExpr (Bool × Nat)) (toExpr q)
  | .var v => mkApp2 (mkConst ``RatPolyCheck.Expr.var [Level.zero])
      (toTypeExpr (Bool × Nat)) (toExpr v)
  | .add e f => mkApp3 (mkConst ``RatPolyCheck.Expr.add [Level.zero])
      (toTypeExpr (Bool × Nat)) (quoteCoefficient e) (quoteCoefficient f)
  | .mul e f => mkApp3 (mkConst ``RatPolyCheck.Expr.mul [Level.zero])
      (toTypeExpr (Bool × Nat)) (quoteCoefficient e) (quoteCoefficient f)

def quoteList (α : Lean.Expr) (xs : List Lean.Expr) : Lean.Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) α x acc)
    (mkApp (mkConst ``List.nil [Level.zero]) α)

def quoteGrunsky (t : GrunskyExprTerm) : Lean.Expr :=
  let n := toExpr t.order
  let values := quoteList coefficientType ((List.finRange t.order).map
    (fun i => quoteCoefficient (t.test i)))
  let idx := mkApp2 (mkConst ``Fin.val []) n (.bvar 0)
  let body := mkApp4 (mkConst ``List.getD [Level.zero]) coefficientType values idx
    (quoteCoefficient (.const 0))
  let fn := mkLambda `i BinderInfo.default (mkApp (mkConst ``Fin []) n) body
  mkApp3 (mkConst ``GrunskyExprTerm.mk []) n (toExpr t.weight) fn

def quoteSquare (t : SquareExprTerm) : Lean.Expr :=
  mkApp2 (mkConst ``SquareExprTerm.mk []) (toExpr t.weight) (quoteCoefficient t.polynomial)

def quoteBlock (b : RationalGramBlock) : Lean.Expr :=
  let gs := quoteList (mkConst ``GrunskyExprTerm []) (b.certificate.grunsky.map quoteGrunsky)
  let ss := quoteList (mkConst ``SquareExprTerm []) (b.certificate.square.map quoteSquare)
  mkApp2 (mkConst ``RationalGramBlock.mk [])
    (mkApp2 (mkConst ``ListRationalGramCertificate.mk []) gs ss)
    (quoteCoefficient b.polynomial)

open Elab Term in
elab "gram_witness% " s:str : term => do
  return quoteBlock (RawGramData.decodeBlock s.getString)

end SpringerLean.GramWitnessQuotation

namespace SpringerLean
noncomputable def quotedEmptyGramBlock : RationalGramBlock := gram_witness% "0,0,0"
theorem quotedEmptyGramBlock_weights : quotedEmptyGramBlock.certificate.weightsCheck = true := by
  decide +kernel
end SpringerLean
#print axioms SpringerLean.quotedEmptyGramBlock_weights
