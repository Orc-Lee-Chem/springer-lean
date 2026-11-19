import SpringerLean.Round18CompactSupport

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The absolute-deviation circle average varies continuously with its
real threshold for any continuous angular boundary curve. -/
theorem continuous_circleAverage_abs_projection_of_continuous_angle
    (W : ℝ → ℂ) (hW : Continuous W) :
    Continuous (fun a : ℝ =>
      (2 * Real.pi)⁻¹ *
        (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), |a - (W θ).re|)) := by
  have hf : Continuous (Function.uncurry
      (fun a θ : ℝ => |a - (W θ).re|)) := by
    fun_prop
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hf 0 (2 * Real.pi))

/-- The actual vertical-line potential integral is continuous in its real
threshold. This is an unconditional boundary regularity consequence. -/
theorem regularExteriorVerticalPotentialDifference_integral_continuous
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ξ : ℂ) :
    Continuous (fun a : ℝ =>
      ∫ y : ℝ, regularExteriorVerticalPotentialDifference F s ξ a y) := by
  let W : ℝ → ℂ := fun θ => conj ξ * rescaleExterior s F (circleMap 0 1 θ)
  let V : ℝ → ℂ := fun θ => ((2 * (circleMap 0 1 θ).re : ℝ) : ℂ)
  have hW := regularExterior_rotated_angle_continuous F hc hs0 hs1 ξ
  have hV := comparisonCircle_angle_continuous
  have hCW := continuous_circleAverage_abs_projection_of_continuous_angle W hW
  have hCV := continuous_circleAverage_abs_projection_of_continuous_angle V hV
  have hformula (a : ℝ) :
      (∫ y : ℝ, regularExteriorVerticalPotentialDifference F s ξ a y) =
        Real.pi *
          ((2 * Real.pi)⁻¹ *
              (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), |a - (W θ).re|) -
           (2 * Real.pi)⁻¹ *
              (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), |a - (V θ).re|)) := by
    rw [regularExteriorVerticalPotentialDifference_integral F hc hs0 hs1 ξ a]
    rw [Real.circleAverage_def, Real.circleAverage_def]
    rfl
  have hcont : Continuous (fun a : ℝ =>
      Real.pi *
        ((2 * Real.pi)⁻¹ *
            (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), |a - (W θ).re|) -
         (2 * Real.pi)⁻¹ *
            (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), |a - (V θ).re|))) :=
    continuous_const.mul (hCW.sub hCV)
  convert hcont using 1
  funext a
  exact hformula a

end SpringerLean
