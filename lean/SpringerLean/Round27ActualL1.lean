import SpringerLean.Round27CurveL1
import SpringerLean.Round17VerticalActual

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The actual compensated difference is globally Lipschitz as an L1
function of the vertical variable when the horizontal coordinate varies. -/
theorem regularExterior_vertical_difference_L1_lipschitz_horizontal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a a' : ℝ) :
    (∫ y : ℝ, |regularExteriorVerticalPotentialDifference F s ξ a y -
      regularExteriorVerticalPotentialDifference F s ξ a' y|) ≤
      2 * Real.pi * |a - a'| := by
  let W : ℝ → ℂ := fun θ => conj ξ * rescaleExterior s F (circleMap 0 1 θ)
  let V : ℝ → ℂ := fun θ => ((2 * (circleMap 0 1 θ).re : ℝ) : ℂ)
  let C : ℝ := (2 * Real.pi)⁻¹
  let K : (ℝ → ℂ) → ℝ → ℝ → ℝ := fun Z x y =>
    ∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), verticalPointKernel x (Z θ) y
  have hW : Continuous W := regularExterior_rotated_angle_continuous F hc hs0 hs1 ξ
  have hV : Continuous V := comparisonCircle_angle_continuous
  have hCa (x y : ℝ) : regularExteriorVerticalPotentialDifference F s ξ x y =
      C * (K W x y - K V x y) := by
    exact regularExteriorVerticalPotentialDifference_eq_compensated
      F hc hs0 hs1 ξ x y
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hCiW (x : ℝ) : Integrable (fun y => K W x y) :=
    (verticalCurveKernel_integrable x W hW).integral_prod_right
  have hCiV (x : ℝ) : Integrable (fun y => K V x y) :=
    (verticalCurveKernel_integrable x V hV).integral_prod_right
  have hleft : Integrable (fun y : ℝ =>
      |regularExteriorVerticalPotentialDifference F s ξ a y -
        regularExteriorVerticalPotentialDifference F s ξ a' y|) :=
    ((regularExteriorVerticalPotentialDifference_integrable F hc hs0 hs1 ξ a).sub
      (regularExteriorVerticalPotentialDifference_integrable F hc hs0 hs1 ξ a')).abs
  have hright : Integrable (fun y : ℝ =>
      C * (|K W a y - K W a' y| + |K V a y - K V a' y|)) := by
    exact ((hCiW a |>.sub (hCiW a')).abs.add
      ((hCiV a).sub (hCiV a')).abs).const_mul C
  have hp (y : ℝ) :
      |regularExteriorVerticalPotentialDifference F s ξ a y -
        regularExteriorVerticalPotentialDifference F s ξ a' y| ≤
        C * (|K W a y - K W a' y| + |K V a y - K V a' y|) := by
    rw [hCa a y, hCa a' y]
    have h := abs_sub (K W a y - K W a' y) (K V a y - K V a' y)
    calc
      |C * (K W a y - K V a y) - C * (K W a' y - K V a' y)| =
        C * |(K W a y - K W a' y) - (K V a y - K V a' y)| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hC0]
          congr 1
          ring
      _ ≤ C * (|K W a y - K W a' y| + |K V a y - K V a' y|) :=
        mul_le_mul_of_nonneg_left h hC0
  calc
    (∫ y : ℝ, |regularExteriorVerticalPotentialDifference F s ξ a y -
      regularExteriorVerticalPotentialDifference F s ξ a' y|) ≤
        ∫ y : ℝ, C * (|K W a y - K W a' y| +
          |K V a y - K V a' y|) :=
      integral_mono_ae hleft hright (Filter.Eventually.of_forall hp)
    _ = C * ((∫ y : ℝ, |K W a y - K W a' y|) +
        (∫ y : ℝ, |K V a y - K V a' y|)) := by
      rw [integral_const_mul]
      congr 1
      exact integral_add
        ((hCiW a).sub (hCiW a')).abs
        ((hCiV a).sub (hCiV a')).abs
    _ ≤ C * ((2 * Real.pi) * (Real.pi * |a - a'|) +
        (2 * Real.pi) * (Real.pi * |a - a'|)) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      exact add_le_add
        (verticalCurveKernel_L1_lipschitz_horizontal a a' W hW)
        (verticalCurveKernel_L1_lipschitz_horizontal a a' V hV)
    _ = 2 * Real.pi * |a - a'| := by
      dsimp [C]
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      ring

end SpringerLean