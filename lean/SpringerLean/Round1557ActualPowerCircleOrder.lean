import SpringerLean.Round1556SelectedTwoAnnulusCubicGains

open scoped ComplexConjugate

namespace SpringerLean

/-- For every inner radius the actual projected positive-power moment is
bounded by the unflattened cosine model. This supplies nonnegative gain
outside the short annulus used for the cubic estimate. -/
theorem actualHarmonic_inner_positivePower_le_cosine
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {m : ℕ} (hm : 1 ≤ m) :
    Real.circleAverage
      (fun z => (max ((conj ξ*actualHarmonic F z).re) 0)^m) 0 r ≤
    Real.circleAverage (fun z : ℂ => (max (2*z.re) 0)^m) 0 r :=
  actualHarmonic_inner_convex_le F hc ξ hξ hr0 hr1
    (fun x : ℝ => (max x 0)^m) (positivePart_pow_convexOn m hm)

end SpringerLean

#print axioms SpringerLean.actualHarmonic_inner_positivePower_le_cosine
