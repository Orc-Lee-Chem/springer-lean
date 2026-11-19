import SpringerLean.Round361BlockGramCore

namespace SpringerLean
open RatPolyCheck

/-- Syntax DATA only. Its meaning is validated by the generic polynomial checker. -/
def certificateHermitianExprSum : List (Rat × CoeffExpr × CoeffExpr) → CoeffExpr
  | [] => .const 0
  | (q, e, f) :: ts => Expr.smartAdd
      (Expr.scale q (.mul e f.conjugate)) (certificateHermitianExprSum ts)

end SpringerLean
