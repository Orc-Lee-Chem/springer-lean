import SpringerLean.Round346OrderedPolynomialCore
import SpringerLean.Round310CompactCertificateData

namespace SpringerLean
open RatPolyCheck

/-- Finite raw data. No mathematical assertions are structure fields. -/
structure ListRationalGramCertificate where
  grunsky : List GrunskyExprTerm
  square : List SquareExprTerm

def ListRationalGramCertificate.body (c : ListRationalGramCertificate) : CoeffExpr :=
  .add
    (Expr.sumList (c.grunsky.map (fun t =>
      Expr.scale t.weight (grunskyDeficitExpr t.order t.test))))
    (Expr.sumList (c.square.map (fun t =>
      Expr.scale t.weight (CoeffExpr.normSq t.polynomial))))

def ListRationalGramCertificate.weightsCheck (c : ListRationalGramCertificate) : Bool :=
  c.grunsky.all (fun t => decide (0 ≤ t.weight)) &&
    c.square.all (fun t => decide (0 ≤ t.weight))

def ListRationalGramCertificate.check (c : ListRationalGramCertificate)
    (k : Nat) (C η : Rat) : Bool :=
  c.weightsCheck && Ordered.check coeffExprVariableOrder (fastGramTargetExpr k C η) c.body

end SpringerLean
