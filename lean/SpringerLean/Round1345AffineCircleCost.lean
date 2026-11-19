import SpringerLean.Round1344GaussianIntegralBound

open MeasureTheory

namespace SpringerLean

private noncomputable def affinePlatformAngle (n : ℕ) (θ : ℝ) : ℝ :=
  (max (39/20 : ℝ) ((2/5)+(8/5)*Real.cos θ))^n

/-- The normalized model circle uses angular, not disk-area, measure.
Shifting the period puts the Gaussian comparison on `[-π,π]`. -/
theorem affinePlatform_circleAverage_eq_principal (n : ℕ) :
    Real.circleAverage
      (fun ζ : ℂ =>
        (max (39/20 : ℝ) ((2/5)+(4/5)*(2*ζ.re)))^n) 0 1 =
      (2*Real.pi)⁻¹ *
        (∫ θ in -Real.pi..Real.pi, affinePlatformAngle n θ) := by
  rw [Real.circleAverage_eq_integral_add (-Real.pi)]
  simp_rw [circleMap_zero_re]
  simp only [one_mul]
  have hpoint (θ : ℝ) :
      (max (39/20 : ℝ)
        ((2/5)+(4/5)*(2*Real.cos (θ + -Real.pi))))^n =
      affinePlatformAngle n (θ + -Real.pi) := by
    unfold affinePlatformAngle
    congr 1
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_comp_add_right]
  simp only [zero_add]
  congr 1
  ring

/-- Coarse one-end circle cost, before the final scalar Catalan
comparison. This bound applies to every order `n ≥ 1`. -/
theorem affinePlatform_circleAverage_le_gaussian
    (n : ℕ) (hn : 1 ≤ n) :
    Real.circleAverage
      (fun ζ : ℂ =>
        (max (39/20 : ℝ) ((2/5)+(4/5)*(2*ζ.re)))^n) 0 1 ≤
      (39/20 : ℝ)^n +
        (2:ℝ)^n * Real.sqrt
          (Real.pi / ((n:ℝ)*(8/5)/Real.pi^2)) / (2*Real.pi) := by
  rw [affinePlatform_circleAverage_eq_principal]
  have h := affinePlatform_principal_integral_le n hn
  have hπ : 0 < 2*Real.pi := by positivity
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hπ.le)
  change (2*Real.pi)⁻¹ *
    (∫ θ in -Real.pi..Real.pi,
      (max (39/20 : ℝ) ((2/5)+(8/5)*Real.cos θ))^n) ≤ _
  calc
    _ ≤ (2*Real.pi)⁻¹ *
      ((2*Real.pi)*(39/20 : ℝ)^n + (2:ℝ)^n *
        Real.sqrt (Real.pi / ((n:ℝ)*(8/5)/Real.pi^2))) := hh
    _ = (39/20 : ℝ)^n +
        (2:ℝ)^n * Real.sqrt
          (Real.pi / ((n:ℝ)*(8/5)/Real.pi^2)) / (2*Real.pi) := by
      field_simp

end SpringerLean

#print axioms SpringerLean.affinePlatform_circleAverage_eq_principal
#print axioms SpringerLean.affinePlatform_circleAverage_le_gaussian
