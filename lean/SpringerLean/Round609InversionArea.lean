import SpringerLean.AnnulusArea

open MeasureTheory

namespace SpringerLean
set_option Elab.async false

theorem complex_injective_image_volume_eq_deriv_lintegral
    (f : ℂ → ℂ) (U : Set ℂ) (hU : MeasurableSet U)
    (hd : ∀ z ∈ U, DifferentiableAt ℂ f z) (hinj : Set.InjOn f U) :
    (∫⁻ z in U, ENNReal.ofReal (‖deriv f z‖ ^ 2)) = volume (f '' U) := by
  have hw : ∀ z ∈ U,
      HasFDerivWithinAt f ((deriv f z) • (1 : ℂ →L[ℝ] ℂ)) U z := by
    intro z hz
    exact (hd z hz).hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt
  convert lintegral_abs_det_fderiv_eq_addHaar_image volume hU hw hinj using 1
  apply setLIntegral_congr_fun hU
  intro z hz
  change ENNReal.ofReal (‖deriv f z‖ ^ 2) =
    ENNReal.ofReal |((deriv f z) • (1 : ℂ →L[ℝ] ℂ)).det|
  rw [complex_mul_real_det, abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq]

/-- Inversion changes planar area by |z|^-4. This is an ENNReal statement,
so it remains meaningful without any prior finiteness assertion. -/
theorem inversion_image_volume_eq_lintegral
    (S : Set ℂ) (hS : MeasurableSet S) (hzero : (0 : ℂ) ∉ S) :
    (∫⁻ z in S, ENNReal.ofReal (‖z‖⁻¹ ^ 4)) =
      volume ((fun z : ℂ => z⁻¹) '' S) := by
  have hnz : ∀ z ∈ S, z ≠ (0 : ℂ) := by
    intro z hz he
    exact hzero (he ▸ hz)
  have hd : ∀ z ∈ S, DifferentiableAt ℂ (fun z : ℂ => z⁻¹) z :=
    fun z hz => (hasDerivAt_inv (hnz z hz)).differentiableAt
  have he := complex_injective_image_volume_eq_deriv_lintegral
    (fun z : ℂ => z⁻¹) S hS hd inv_injective.injOn
  convert he using 1
  apply setLIntegral_congr_fun hS
  intro z hz
  change ENNReal.ofReal (‖z‖⁻¹ ^ 4) =
    ENNReal.ofReal (‖deriv (fun z : ℂ => z⁻¹) z‖ ^ 2)
  rw [(hasDerivAt_inv (hnz z hz)).deriv]
  simp only [norm_neg, norm_inv, norm_pow, ← inv_pow, ← pow_mul]

end SpringerLean
