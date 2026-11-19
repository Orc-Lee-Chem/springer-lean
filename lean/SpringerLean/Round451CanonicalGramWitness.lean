import SpringerLean.Round407QuotedGramWitness

/- Canonical rational DATA avoids repeatedly normalizing input fractions.
The denominator and coprimality proofs are ordinary decide/rfl terms, which
the kernel checks when the enclosing definition is declared. No native
Boolean result is accepted as a mathematical assertion. -/
namespace SpringerLean.CanonicalGramWitness
open Lean Meta
open GramWitnessQuotation

def quoteRat (q : Rat) : MetaM Lean.Expr := do
  let num := toExpr q.num
  let den := mkNatLit q.den
  let hn ← mkDecideProof (← mkAppM ``Ne #[den, mkNatLit 0])
  let hc ← mkDecideProof (mkApp2 (mkConst ``Nat.Coprime []) (mkNatLit q.num.natAbs) den)
  return mkApp4 (mkConst ``Rat.mk' []) num den hn hc

def quoteCoefficient : CoeffExpr → MetaM Lean.Expr
  | .const q => do
      return mkApp2 (mkConst ``RatPolyCheck.Expr.const [Level.zero])
        (toTypeExpr (Bool × Nat)) (← quoteRat q)
  | .var v => pure <| mkApp2 (mkConst ``RatPolyCheck.Expr.var [Level.zero])
      (toTypeExpr (Bool × Nat)) (toExpr v)
  | .add e f => do
      return mkApp3 (mkConst ``RatPolyCheck.Expr.add [Level.zero])
        (toTypeExpr (Bool × Nat)) (← quoteCoefficient e) (← quoteCoefficient f)
  | .mul e f => do
      return mkApp3 (mkConst ``RatPolyCheck.Expr.mul [Level.zero])
        (toTypeExpr (Bool × Nat)) (← quoteCoefficient e) (← quoteCoefficient f)

def quoteGrunsky (t : GrunskyExprTerm) : MetaM Lean.Expr := do
  let n := toExpr t.order
  let elements ← (List.finRange t.order).mapM (fun i => quoteCoefficient (t.test i))
  let values := quoteList coefficientType elements
  let idx := mkApp2 (mkConst ``Fin.val []) n (.bvar 0)
  let body := mkApp4 (mkConst ``List.getD [Level.zero]) coefficientType values idx
    (← quoteCoefficient (.const 0))
  let fn := mkLambda `i BinderInfo.default (mkApp (mkConst ``Fin []) n) body
  return mkApp3 (mkConst ``GrunskyExprTerm.mk []) n (← quoteRat t.weight) fn

def quoteSquare (t : SquareExprTerm) : MetaM Lean.Expr := do
  return mkApp2 (mkConst ``SquareExprTerm.mk []) (← quoteRat t.weight)
    (← quoteCoefficient t.polynomial)

def quoteBlock (b : RationalGramBlock) : MetaM Lean.Expr := do
  let gs := quoteList (mkConst ``GrunskyExprTerm []) (← b.certificate.grunsky.mapM quoteGrunsky)
  let ss := quoteList (mkConst ``SquareExprTerm []) (← b.certificate.square.mapM quoteSquare)
  return mkApp2 (mkConst ``RationalGramBlock.mk [])
    (mkApp2 (mkConst ``ListRationalGramCertificate.mk []) gs ss)
    (← quoteCoefficient b.polynomial)

open Elab Term in
elab "canonical_gram_witness% " s:str : term => do
  quoteBlock (RawGramData.decodeBlock s.getString)

end SpringerLean.CanonicalGramWitness

namespace SpringerLean
noncomputable def canonicalEmptyGramBlock : RationalGramBlock :=
  canonical_gram_witness% "0,0,0"
theorem canonicalEmptyGramBlock_weights :
    canonicalEmptyGramBlock.certificate.weightsCheck = true := by decide +kernel
end SpringerLean
#print axioms SpringerLean.canonicalEmptyGramBlock_weights
