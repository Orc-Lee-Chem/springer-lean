import SpringerLean.Round488ScaledGramTreeCore

namespace SpringerLean
open RatPolyCheck

/-- Proposed coefficients only. Entry correctness is independently checked. -/
abbrev GrunskyCoeffCache := List ((Nat × Nat) × CoeffExpr)

def cachedGrunskyCoeffExpr : GrunskyCoeffCache → Nat → Nat → CoeffExpr
  | [], m, l => fastLogGrunskyCoeffExpr m l
  | ((i,j),e) :: cs, m, l =>
      if m = i ∧ l = j then e else cachedGrunskyCoeffExpr cs m l

def grunskyCoeffCacheChecks (cs : GrunskyCoeffCache) : Prop :=
  ∀ entry ∈ cs, Ordered.check coeffExprVariableOrder entry.2
    (fastLogGrunskyCoeffExpr entry.1.1 entry.1.2) = true

def cachedGrunskyDeficitExpr (cs : GrunskyCoeffCache)
    (N : Nat) (x : Fin N → CoeffExpr) : CoeffExpr :=
  Expr.sub
    (Expr.sumFin (fun i : Fin N => Expr.scale (((i.val + 1 : Nat) : Rat)⁻¹)
      (CoeffExpr.normSq (x i))))
    (Expr.sumFin (fun j : Fin N => Expr.scale ((j.val + 1 : Nat) : Rat)
      (CoeffExpr.normSq (Expr.sumFin (fun i : Fin N => Expr.mulUnlessRightZero
        (fun _ => cachedGrunskyCoeffExpr cs (j.val + 1) (i.val + 1)) (x i))))))

def ListRationalGramCertificate.cachedBody
    (c : ListRationalGramCertificate) (cs : GrunskyCoeffCache) : CoeffExpr :=
  .add
    (Expr.sumList (c.grunsky.map (fun t =>
      Expr.scale t.weight (cachedGrunskyDeficitExpr cs t.order t.test))))
    (Expr.sumList (c.square.map (fun t =>
      Expr.scale t.weight (CoeffExpr.normSq t.polynomial))))

def RationalGramBlock.cachedCheck (b : RationalGramBlock) (cs : GrunskyCoeffCache) : Bool :=
  b.certificate.weightsCheck && Ordered.check coeffExprVariableOrder
    b.polynomial (b.certificate.cachedBody cs)

def RationalScaledGramTree.cachedCheck (cs : GrunskyCoeffCache) : RationalScaledGramTree → Bool
  | .zero => true
  | .leaf q b => decide (0 ≤ q) && b.cachedCheck cs
  | .add p l r => l.cachedCheck cs && (r.cachedCheck cs &&
      Ordered.check coeffExprVariableOrder p (.add l.polynomial r.polynomial))

theorem RationalScaledGramTree.add_cachedCheck
    (cs : GrunskyCoeffCache) (p : CoeffExpr) (l r : RationalScaledGramTree)
    (hl : l.cachedCheck cs = true) (hr : r.cachedCheck cs = true)
    (he : Ordered.check coeffExprVariableOrder p (.add l.polynomial r.polynomial) = true) :
    (RationalScaledGramTree.add p l r).cachedCheck cs = true := by
  simp only [cachedCheck, hl, hr, he, Bool.and_self]

end SpringerLean
