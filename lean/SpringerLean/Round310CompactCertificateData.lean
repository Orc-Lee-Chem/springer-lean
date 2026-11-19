import SpringerLean.Round299CertificateData

namespace SpringerLean
open RatPolyCheck

/-- Compact expression DATA: eliminate literal unit/zero factors before
normalization. Correctness of every resulting witness is checked globally. -/
def certificateCompactMul (e f : CoeffExpr) : CoeffExpr :=
  match e, f with
  | .const a, _ => if a = 0 then .const 0 else if a = 1 then f else .mul e f
  | _, .const b => if b = 0 then .const 0 else if b = 1 then e else .mul e f
  | _, _ => .mul e f

def certificateCompactPow (e : CoeffExpr) : Nat → CoeffExpr
  | 0 => .const 1
  | n + 1 => certificateCompactMul e (certificateCompactPow e n)

def certificateCompactMonomialExpr : Nat → List Nat → CoeffExpr
  | _, [] => .const 1
  | j, e :: es =>
      if e = 0 then certificateCompactMonomialExpr (j + 1) es else
      certificateCompactMul (certificateCompactPow (.var (false, j)) e)
        (certificateCompactMonomialExpr (j + 1) es)

def certificateCompactLinearExpr : List (Rat × List Nat) → CoeffExpr
  | [] => .const 0
  | (q, e) :: ts => Expr.smartAdd
      (certificateCompactMul (.const q) (certificateCompactMonomialExpr 1 e))
      (certificateCompactLinearExpr ts)

end SpringerLean
