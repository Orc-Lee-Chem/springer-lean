import SpringerLean.Round2095ExteriorGreenRegularity

open MeasureTheory Set Real

namespace SpringerLean

/-- The circular mean of the actual Green coordinate is the radial
logarithmic hinge moment plus the reference radius logarithm. Absolute
integrability is established before swapping the two laws. -/
theorem exteriorGreenCoordinate_circleAverage_eq_radial_hinge
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (r : ℝ) (hr : 0 < r) :
    circleAverage (exteriorGreenCoordinate F) 0 r =
      Real.log r + ∫ z, Real.posLog (r⁻¹ * ‖z‖) ∂actualExteriorBoundaryProbability F := by
  let μ := actualExteriorBoundaryProbability F
  let J := Ioc (0 : ℝ) (2*π)
  let α := volume.restrict J
  let H (θ : ℝ) (z : ℂ) := log ‖z - circleMap 0 r θ‖
  have hprob : IsProbabilityMeasure μ := ⟨actualExteriorBoundaryProbability_univ F hF⟩
  have hα : IsFiniteMeasure α := isFiniteMeasure_restrict.mpr (by
    dsimp [J]
    rw [Real.volume_Ioc]
    finiteness)
  have hαreal : α.real univ = 2*π := by
    rw [show α = volume.restrict J from rfl, measureReal_restrict_apply_univ]
    simp [J, volume_real_Ioc_of_le two_pi_pos.le]
  have hμ : exteriorOmitted F ∈ ae μ := actualExteriorBoundaryProbability_ae_mem_omitted F hF
    (exteriorOmitted_isCompact F hF).isClosed
  have hmeas : Measurable (Function.uncurry H) := by
    unfold H Function.uncurry
    fun_prop
  have hslice (z : ℂ) : Integrable (fun θ => H θ z) α := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).mp
    simpa [H, CircleIntegrable, norm_sub_rev] using
      (circleIntegrable_log_norm_sub_const (a := z) (c := 0) r)
  have heval (z : ℂ) : (∫ θ, H θ z ∂α) = (2*π)*(log r + posLog (r⁻¹*‖z‖)) := by
    have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := z) (c := 0) hr.ne'
    rw [circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul,
      zero_sub, norm_neg] at h
    have hx := congrArg (fun a : ℝ => (2*π)*a) h
    simpa only [H, α, J, norm_sub_rev, ← mul_assoc, mul_inv_cancel₀ two_pi_pos.ne', one_mul] using hx
  let M := log (3+r)
  have hM : 0 ≤ M := by
    change 0 ≤ log (3+r)
    exact Real.log_nonneg (by linarith)
  have hasBound : ∀ᵐ z ∂μ, (∫ θ, ‖H θ z‖ ∂α) ≤ (2*π)*(2*M-log r) := by
    filter_upwards [hμ] with z hz
    have hp θ : (H θ z)⁺ ≤ M := by
      change max (log ‖z-circleMap 0 r θ‖) 0 ≤ M
      apply max_le _ hM
      by_cases hzero : z-circleMap 0 r θ = 0
      · simpa [hzero] using hM
      apply Real.log_le_log (norm_pos_iff.mpr hzero)
      have hθ : ‖circleMap 0 r θ‖ = r := by simp [abs_of_pos hr]
      exact (norm_sub_le _ _).trans (by linarith [exteriorOmitted_norm_le_two F hF hz])
    have hpos := integral_mono (hslice z).pos_part (integrable_const M) hp
    rw [integral_const, smul_eq_mul, hαreal] at hpos
    change (∫ θ, (H θ z)⁺ ∂α) ≤ (2*π)*M at hpos
    have ha := integral_abs_eq_two_mul_integral_posPart_sub_integral (hslice z)
    have hb : (2*π)*log r ≤ ∫ θ, H θ z ∂α := by
      rw [heval]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right posLog_nonneg) two_pi_pos.le
    simp only [Real.norm_eq_abs]
    nlinarith only [ha, hb, hpos]
  have hlogI : Integrable (Function.uncurry H) (α.prod μ) := by
    apply (integrable_prod_iff' hmeas.aestronglyMeasurable).mpr
    refine ⟨.of_forall hslice,?_⟩
    have hm : AEStronglyMeasurable (fun z => ∫ θ, ‖H θ z‖ ∂α) μ :=
      (hmeas.norm.stronglyMeasurable.integral_prod_left' (μ := α)).aestronglyMeasurable
    apply Integrable.mono (integrable_const (max ((2*π)*(2*M-log r)) 0)) hm
    filter_upwards [hasBound] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)),
      Real.norm_of_nonneg (le_max_right _ _)]
    exact hz.trans (le_max_left _ _)
  have hhinge : Integrable (fun z : ℂ => posLog (r⁻¹*‖z‖)) μ := by
    have hc : Continuous (fun z : ℂ => posLog (r⁻¹*‖z‖)) :=
      continuous_posLog.comp (continuous_const.mul continuous_norm)
    apply Integrable.mono (integrable_const (posLog (r⁻¹*2))) hc.aestronglyMeasurable
    filter_upwards [hμ] with z hz
    simp only [Real.norm_of_nonneg (posLog_nonneg : 0 ≤ posLog (_ : ℝ))]
    apply posLog_le_posLog (neg_one_lt_zero.le.trans (mul_nonneg (inv_nonneg.mpr hr.le) (norm_nonneg _)))
    exact mul_le_mul_of_nonneg_left (exteriorOmitted_norm_le_two F hF hz) (inv_nonneg.mpr hr.le)
  have hp (θ : ℝ) : exteriorGreenCoordinate F (circleMap 0 r θ) = ∫ z, H θ z ∂μ :=
    exteriorGreenCoordinate_eq_radial_potential F hF _
  rw [circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul]
  simp_rw [hp]
  change (2*π)⁻¹ * (∫ θ, ∫ z, H θ z ∂μ ∂α) = _
  rw [integral_integral_swap hlogI]
  simp_rw [heval]
  rw [integral_const_mul, integral_add (integrable_const (log r)) hhinge, integral_const,
    probReal_univ, one_smul, ← mul_assoc, inv_mul_cancel₀ two_pi_pos.ne', one_mul]

end SpringerLean
