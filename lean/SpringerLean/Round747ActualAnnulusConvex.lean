import SpringerLean.Round746AnnulusCircleOrder
import SpringerLean.Round730ActualInnerConvex

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false

/-- An actual source-annulus comparison. The unit direction and convex
test are fixed on THIS annulus and may be chosen afresh on another one.
No circle-comparison, regularization or boundary premise remains. -/
theorem actualHarmonic_annulus_convex_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (ψ : ℝ → ℝ) (hψ : ConvexOn ℝ univ ψ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    Real.pi⁻¹*(∫ z in greenPolarRegion a b, ψ ((conj ξ*actualHarmonic F z).re)) ≤
      Real.pi⁻¹*(∫ z in greenPolarRegion a b, ψ (2*z.re)) := by
  have hψc : Continuous ψ := by
    simpa only [continuousOn_univ] using ConvexOn.continuousOn isOpen_univ hψ
  have hsub : closedBall (0 : ℂ) b ⊆ ball 0 1 := by
    intro z hz
    have hn : ‖z‖ ≤ b := by simpa only [mem_closedBall, dist_zero_right] using hz
    simpa only [mem_ball, dist_zero_right] using hn.trans_lt hb
  have hH := (actualHarmonic_continuousOn_unitBall F hc).mono hsub
  have hX : ContinuousOn (fun z => ψ ((conj ξ*actualHarmonic F z).re)) (closedBall (0 : ℂ) b) :=
    hψc.comp_continuousOn (Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hH))
  have hY : ContinuousOn (fun z : ℂ => ψ (2*z.re)) (closedBall (0 : ℂ) b) :=
    (hψc.comp (by fun_prop : Continuous (fun z : ℂ => 2*z.re))).continuousOn
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ Real.pi⁻¹)
  apply greenPolarRegion_integral_le_of_circleAverage_le _ _ ha hX hY
  intro r hr
  exact actualHarmonic_inner_convex_le F hc ξ hξ (ha.trans hr.1) (hr.2.trans_lt hb) ψ hψ

end SpringerLean

#print axioms SpringerLean.actualHarmonic_annulus_convex_le
