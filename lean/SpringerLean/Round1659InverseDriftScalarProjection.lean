import SpringerLean.Round1658ActualModulusGradientPairing
import Mathlib.Analysis.Calculus.FDeriv.Norm

open scoped ComplexConjugate

namespace SpringerLean

/-- A scalar gradient paired with the inverse-conjugate field has exactly
one factor of the reciprocal filling modulus. -/
theorem inverseConjugate_scalar_fderiv_abs_le
    (f : ℂ → ℝ) (z H : ℂ) :
    |(fderiv ℝ f z) (1:ℂ)*((conj H)⁻¹).re +
      (fderiv ℝ f z) Complex.I*((conj H)⁻¹).im| ≤
      ‖fderiv ℝ f z‖ / ‖H‖ := by
  let Q := (conj H)⁻¹
  have h := scalar_fderiv_dot_gradient_abs_le f z Q.re Q.im
  have hQ : Real.sqrt (Q.re^2+Q.im^2) = ‖Q‖ := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    ring
  rw [hQ] at h
  have hQnorm : ‖Q‖ = 1/‖H‖ := by simp [Q, norm_inv]
  rw [hQnorm] at h
  simpa [Q, div_eq_mul_inv] using h

/-- The source-radius derivative paired with the inverse-conjugate
drift costs at most one reciprocal filling modulus. -/
theorem inverseConjugate_source_radius_fderiv_abs_le
    (z H : ℂ) (hz : z ≠ 0) :
    |(fderiv ℝ (fun w : ℂ => ‖w‖) z) (1:ℂ)*((conj H)⁻¹).re +
      (fderiv ℝ (fun w : ℂ => ‖w‖) z) Complex.I*((conj H)⁻¹).im| ≤
      1 / ‖H‖ := by
  have h := inverseConjugate_scalar_fderiv_abs_le
    (fun w : ℂ => ‖w‖) z H
  have hdiff : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) z :=
    differentiableAt_id.norm (𝕜 := ℂ) hz
  rw [norm_fderiv_norm hdiff] at h
  exact h

end SpringerLean

#print axioms SpringerLean.inverseConjugate_scalar_fderiv_abs_le
#print axioms SpringerLean.inverseConjugate_source_radius_fderiv_abs_le
