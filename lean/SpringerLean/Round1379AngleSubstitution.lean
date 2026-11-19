import SpringerLean.Round1378AngleDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open MeasureTheory

namespace SpringerLean

/-- The angular substitution has no endpoint singularity: only the open
arc derivative is used by the interval-integral change-of-variables rule. -/
theorem coarseAngle_active_integral_substitution (n : ℕ) :
    (∫ θ in (0:ℝ)..coarseAngleAlpha,
      coarseInverseRadius (2*Real.cos θ)^n) =
    ∫ v in (0:ℝ)..coarseAngleBeta,
      (2*Real.cos v)^n * deriv coarseAnglePhi v := by
  have hβ0 := coarseAngleBeta_range.1
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0:ℝ)) (b := coarseAngleBeta)
    (f := coarseAnglePhi) (f' := deriv coarseAnglePhi)
    (g := fun θ : ℝ => coarseInverseRadius (2*Real.cos θ)^n)
    coarseAnglePhi_continuous.continuousOn
    (by
      intro x hx
      have hxin : x ∈ Set.Ioo 0 coarseAngleBeta := by
        simpa [min_eq_left hβ0, max_eq_right hβ0] using hx
      exact (coarseAnglePhi_differentiableAt hxin.1.le hxin.2.le).hasDerivAt)
    (by
      intro x hx
      have hxin : x ∈ Set.Ioo 0 coarseAngleBeta := by
        simpa [min_eq_left hβ0, max_eq_right hβ0] using hx
      exact (coarseAnglePhi_deriv_bounds hxin.1 hxin.2).1)
  rw [coarseAnglePhi_zero, coarseAnglePhi_beta] at hchange
  have hcongr :
      (∫ v in (0:ℝ)..coarseAngleBeta,
        (coarseInverseRadius (2*Real.cos (coarseAnglePhi v))^n) *
          deriv coarseAnglePhi v) =
      ∫ v in (0:ℝ)..coarseAngleBeta,
        (2*Real.cos v)^n * deriv coarseAnglePhi v := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Set.Icc 0 coarseAngleBeta := by simpa [hβ0] using hv
    dsimp
    rw [coarseAnglePhi_profile hv'.1 hv'.2]
  simpa only [Function.comp_apply] using hchange.symm.trans hcongr

end SpringerLean

#print axioms SpringerLean.coarseAngle_active_integral_substitution
