import SpringerLean.Round1914ActualProjectionDeficit

open MeasureTheory Set
open scoped ComplexConjugate

namespace SpringerLean

/-- The analytic interpolation test applies to the actual boundary trace
of each original exterior map, with no convexity or monotonicity premise
left to the caller. -/
theorem actualRadialTrace_interpolation_test_le_cosine
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {a θ : ℝ} (ha : 4 ≤ a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (2 * Real.pi)⁻¹ *
      (∫ t in Ioo (-Real.pi) Real.pi,
        interpolationPowerTest a θ
          (‖actualExteriorRadialTrace F t‖ / 2) +
        ((a + 2 * θ) * θ * (1 - θ) * interpolationCurvatureConstant a) *
          ((conj ξ * actualExteriorRadialTrace F t).re / 2) ^ 2) ≤
      Real.circleAverage
        (fun z : ℂ => interpolationPowerTest a θ |z.re| +
          ((a + 2 * θ) * θ * (1 - θ) * interpolationCurvatureConstant a) *
            z.re ^ 2) 0 1 := by
  have hp : 0 ≤ a + 2 * θ := by linarith
  have ha0 : 0 ≤ a := by linarith
  have ha2 : 0 ≤ a + 2 := by linarith
  have hcont : Continuous (interpolationPowerTest a θ) := by
    unfold interpolationPowerTest
    fun_prop
  exact actualRadialTrace_compensated_localConvexTest_le_cosine
    F hc ξ hξ (interpolationPowerTest a θ) hcont
    (interpolationPowerTest_antitoneOn ha hθ0 hθ1)
    ((a + 2 * θ) * θ * (1 - θ) * interpolationCurvatureConstant a)
    (interpolationPowerTest_compensated_localConvex ha hθ0 hθ1)

end SpringerLean

#print axioms SpringerLean.actualRadialTrace_interpolation_test_le_cosine
