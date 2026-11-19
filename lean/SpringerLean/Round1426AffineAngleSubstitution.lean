import SpringerLean.Round1425AffineAngleDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open MeasureTheory

namespace SpringerLean
set_option maxHeartbeats 200000

theorem refinedAffine_angle_zero (γ : ℝ) :
    refinedAffineAngle γ 0 = 0 := by
  simp [refinedAffineAngle]

theorem refinedAffine_angle_continuous (γ : ℝ) :
    Continuous (refinedAffineAngle γ) := by
  unfold refinedAffineAngle
  fun_prop

/-- Closed-interval angular substitution with only an interior
derivative. The arcsine endpoint at zero needs no special derivative
theorem. -/
theorem refinedAffine_angle_integral_substitution
    {γ b : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hb0 : 0 ≤ b) (hb : b ≤ Real.pi/2)
    (hshort : 2-2*Real.cos b < γ*(51/500:ℝ))
    (g : ℝ → ℝ) :
    (∫ θ in (0:ℝ)..refinedAffineAngle γ b, g θ) =
      ∫ φ in (0:ℝ)..b,
        g (refinedAffineAngle γ φ) *
          deriv (refinedAffineAngle γ) φ := by
  have hbπ : b ≤ Real.pi := by linarith [Real.pi_pos]
  have hshortAt (φ : ℝ) (hφ0 : 0 < φ) (hφb : φ < b) :
      2-2*Real.cos φ < γ*(51/500:ℝ) := by
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi
      hφ0.le hbπ hφb.le
    linarith
  have hchange :=
    intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0:ℝ)) (b := b)
      (f := refinedAffineAngle γ)
      (f' := deriv (refinedAffineAngle γ))
      (g := g)
      (refinedAffine_angle_continuous γ).continuousOn
      (by
        intro φ hφ
        have hφ' : φ ∈ Set.Ioo 0 b := by
          simpa [min_eq_left hb0,max_eq_right hb0] using hφ
        exact (refinedAffine_angle_differentiableAt hγ hφ'.1.le
          (hφ'.2.le.trans hb) (hshortAt φ hφ'.1 hφ'.2).le).hasDerivAt)
      (by
        intro φ hφ
        have hφ' : φ ∈ Set.Ioo 0 b := by
          simpa [min_eq_left hb0,max_eq_right hb0] using hφ
        rw [refinedAffine_angle_deriv_formula hγ hγ1 hφ'.1
          (hφ'.2.trans_le hb) (hshortAt φ hφ'.1 hφ'.2)]
        positivity)
  rw [refinedAffine_angle_zero] at hchange
  simpa only [Function.comp_apply] using hchange.symm

end SpringerLean

#print axioms SpringerLean.refinedAffine_angle_integral_substitution
