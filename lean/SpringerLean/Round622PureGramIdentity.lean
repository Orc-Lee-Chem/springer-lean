import SpringerLean.Round530CachedGramCore
import SpringerLean.Round348OrderedPolynomialSemantics
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Algebra.Rat

namespace SpringerLean
open RatPolyCheck

/-- The polynomial identity predicate alone, independent of all actual-map
analysis. It unfolds to the same universal equality used by the actual
Gram soundness theorem. -/
def rawCoeffExprIdentity (e f : CoeffExpr) : Prop :=
  ∀ env : (Bool × Nat) → ℂ, e.eval env = f.eval env

end SpringerLean
