import SpringerLean.Round18FiniteConvex
import SpringerLean.Round18CompactSupport

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- Every finite convex hinge test follows for the actual regularized
boundary once the still-open all-threshold vertical sign is supplied.
The sign is displayed explicitly in the type; this is not a final
unconditional boundary convex-order theorem. -/
theorem regularExterior_finiteHingeTest_le_of_vertical_sign
    {ι : Type*} (S : Finset ι) (w t : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ξ : ℂ)
    (hsign : ∀ a : ℝ,
      (∫ y : ℝ, regularExteriorVerticalPotentialDifference F s ξ a y) ≤ 0)
    (p q : ℝ) :
    Real.circleAverage
      (fun ζ => finiteHingeTest S w t p q
        ((conj ξ * rescaleExterior s F ζ).re)) 0 1 ≤
    Real.circleAverage
      (fun ζ : ℂ => finiteHingeTest S w t p q (2 * ζ.re)) 0 1 := by
  let X : ℂ → ℝ := fun ζ => (conj ξ * rescaleExterior s F ζ).re
  let Y : ℂ → ℝ := fun ζ => 2 * ζ.re
  have hX : ContinuousOn X (sphere (0 : ℂ) 1) :=
    regularExterior_projection_continuousOn_sphere F hc hs0 hs1 ξ
  have hY : ContinuousOn Y (sphere (0 : ℂ) 1) := by fun_prop
  have hmean : Real.circleAverage X 0 1 = Real.circleAverage Y 0 1 := by
    rw [rescaleExterior_projected_boundary_circleAverage_zero F hc hs0 hs1 ξ,
      comparisonCircle_projection_circleAverage_zero (by norm_num)]
  exact circleAverage_finiteHingeTest_le S w t X Y hX hY hmean hw
    (fun i _ => regularExterior_positivePart_le_of_vertical_sign
      F hc hs0 hs1 ξ (t i) (hsign (t i))) p q

end SpringerLean
