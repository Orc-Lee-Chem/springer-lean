import SpringerLean.Round363SparseBivariateCore
import SpringerLean.Round356ListGramCore

namespace SpringerLean
open RatPolyCheck

def sparseGrunskyDeficitExpr (N : Nat) (x : Fin N → CoeffExpr) : CoeffExpr :=
  Expr.sub
    (Expr.sumFin (fun i : Fin N => Expr.scale (((i.val + 1 : Nat) : Rat)⁻¹)
      (CoeffExpr.normSq (x i))))
    (Expr.sumFin (fun j : Fin N => Expr.scale ((j.val + 1 : Nat) : Rat)
      (CoeffExpr.normSq (Expr.sumFin (fun i : Fin N => Expr.mulUnlessRightZero
        (fun _ => fastLogGrunskyCoeffExpr (j.val + 1) (i.val + 1)) (x i))))))

def ListRationalGramCertificate.sparseBody (c : ListRationalGramCertificate) : CoeffExpr :=
  .add
    (Expr.sumList (c.grunsky.map (fun t =>
      Expr.scale t.weight (sparseGrunskyDeficitExpr t.order t.test))))
    (Expr.sumList (c.square.map (fun t =>
      Expr.scale t.weight (CoeffExpr.normSq t.polynomial))))

def ListRationalGramCertificate.sparseCheck (c : ListRationalGramCertificate)
    (k : Nat) (C η : Rat) : Bool :=
  c.weightsCheck && Ordered.check coeffExprVariableOrder
    (fastGramTargetExpr k C η) c.sparseBody

end SpringerLean
