import SpringerLean.Round361BlockGramCore

namespace SpringerLean
open RatPolyCheck

/-- A data-only addition tree. Every leaf and local addition is checked. -/
inductive RationalGramTree where
  | zero
  | leaf (block : RationalGramBlock)
  | add (polynomial : CoeffExpr) (left right : RationalGramTree)

def RationalGramTree.polynomial : RationalGramTree → CoeffExpr
  | .zero => .const 0
  | .leaf b => b.polynomial
  | .add p _ _ => p

def RationalGramTree.check : RationalGramTree → Bool
  | .zero => true
  | .leaf b => b.check
  | .add p l r => l.check && (r.check &&
      Ordered.check coeffExprVariableOrder p (.add l.polynomial r.polynomial))

theorem RationalGramTree.add_check (p : CoeffExpr) (l r : RationalGramTree)
    (hl : l.check = true) (hr : r.check = true)
    (he : Ordered.check coeffExprVariableOrder p (.add l.polynomial r.polynomial) = true) :
    (RationalGramTree.add p l r).check = true := by
  simp only [check, hl, hr, he, Bool.and_self]

end SpringerLean
