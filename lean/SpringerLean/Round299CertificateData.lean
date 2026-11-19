import SpringerLean.Round321CertificateCore

namespace SpringerLean
open RatPolyCheck

/-- Syntax for a monomial in the actual forward coefficients b₁,b₂,… . -/
def certificateMonomialExpr : Nat → List Nat → CoeffExpr
  | _, [] => .const 1
  | j, e :: es => .mul (Expr.pow (.var (false, j)) e)
      (certificateMonomialExpr (j + 1) es)

/-- Finite rational linear combination, solely expression DATA. -/
def certificateLinearExpr : List (Rat × List Nat) → CoeffExpr
  | [] => .const 0
  | (q, e) :: ts => .add (Expr.scale q (certificateMonomialExpr 1 e))
      (certificateLinearExpr ts)

end SpringerLean

namespace SpringerLean
instance : Inhabited CoeffExpr := ⟨.const 0⟩
instance : Inhabited GrunskyExprTerm := ⟨{order := 0, weight := 0, test := fun i => Fin.elim0 i}⟩
instance : Inhabited SquareExprTerm := ⟨{weight := 0, polynomial := .const 0}⟩
def certificateVec {α : Type _} [Inhabited α] (l : List α) (i : Fin l.length) : α :=
  l.getD i.val default
end SpringerLean
