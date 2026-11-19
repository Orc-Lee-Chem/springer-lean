import SpringerLean.Round63ActualReciprocal

namespace SpringerLean

/-- Finite coefficients predicted by `log ((z-ζ)/(F(z)-F(ζ)))` through bidegree (3,3).
Their identification with that two-variable analytic kernel remains a separate theorem. -/
noncomputable def schoberQ11 (b1 : ℂ) : ℂ := b1
noncomputable def schoberQ12 (b2 : ℂ) : ℂ := b2
noncomputable def schoberQ13 (b3 : ℂ) : ℂ := b3
noncomputable def schoberQ22 (b1 b3 : ℂ) : ℂ := b3 + b1 ^ 2 / 2
noncomputable def schoberQ33 (b1 b2 b3 b5 : ℂ) : ℂ :=
  b5 + b1 * b3 + b2 ^ 2 + b1 ^ 3 / 3

/-- Linear, quadratic and cubic contributions after applying the order-three
functional in both variables. The normalization factors are 1, 1/2!, 1/3!. -/
noncomputable def schoberFiniteLinear (b1 b2 b3 b5 : ℂ) : ℂ :=
  b1 ^ 2 * schoberQ11 b1 + 2 * b1 * schoberQ13 b3 +
    schoberQ33 b1 b2 b3 b5
noncomputable def schoberFiniteQuadratic (b1 b2 b3 : ℂ) : ℂ :=
  schoberQ11 b1 * schoberQ22 b1 b3 + (schoberQ12 b2) ^ 2
noncomputable def schoberFiniteCubic (b1 : ℂ) : ℂ :=
  (schoberQ11 b1) ^ 3 / 6

/-- Exact finite algebra, including the minus convention for the inverse expansion. -/
theorem schoberFiniteContributions_eq_fifthPolynomial
    (b1 b2 b3 b5 : ℂ) :
    schoberFiniteLinear b1 b2 b3 b5 +
        schoberFiniteQuadratic b1 b2 b3 +
        schoberFiniteCubic b1 =
      b5 + 4 * b1 * b3 + 2 * b2 ^ 2 + 2 * b1 ^ 3 := by
  unfold schoberFiniteLinear schoberFiniteQuadratic schoberFiniteCubic
    schoberQ11 schoberQ12 schoberQ13 schoberQ22 schoberQ33
  ring

/-- The independently read fifth inverse coefficient equals the finite
three-term algebraic expression. This does not yet assert the Grunsky bound. -/
theorem exteriorInverseCoeff_five_eq_schoberFiniteContributions
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    exteriorInverseCoeff F 5 =
      schoberFiniteLinear
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 5) +
      schoberFiniteQuadratic
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) +
      schoberFiniteCubic (exteriorForwardCoeff F 1) := by
  rw [schoberFiniteContributions_eq_fifthPolynomial]
  exact exteriorInverseCoeff_five_eq_forward F hc

end SpringerLean