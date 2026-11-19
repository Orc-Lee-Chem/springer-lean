import SpringerLean.Round470GramTreeCore

namespace SpringerLean
open RatPolyCheck

/-- Data only. Rational weights stay outside the integer-normalized leaves. -/
inductive RationalScaledGramTree where
  | zero
  | leaf (weight : Rat) (block : RationalGramBlock)
  | add (polynomial : CoeffExpr) (left right : RationalScaledGramTree)

def RationalScaledGramTree.polynomial : RationalScaledGramTree → CoeffExpr
  | .zero => .const 0
  | .leaf q b => .mul (.const q) b.polynomial
  | .add p _ _ => p

def RationalScaledGramTree.check : RationalScaledGramTree → Bool
  | .zero => true
  | .leaf q b => decide (0 ≤ q) && b.check
  | .add p l r => l.check && (r.check &&
      Ordered.check coeffExprVariableOrder p (.add l.polynomial r.polynomial))

theorem RationalScaledGramTree.add_check (p : CoeffExpr) (l r : RationalScaledGramTree)
    (hl : l.check = true) (hr : r.check = true)
    (he : Ordered.check coeffExprVariableOrder p (.add l.polynomial r.polynomial) = true) :
    (RationalScaledGramTree.add p l r).check = true := by
  simp only [check, hl, hr, he, Bool.and_self]

end SpringerLean
