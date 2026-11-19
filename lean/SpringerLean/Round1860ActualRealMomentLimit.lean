import SpringerLean.Round1849ActualRadialTwoSlit

open MeasureTheory Filter Set
open scoped Topology

namespace SpringerLean

/-- Every nonnegative real boundary exponent passes from the actual
exterior circles to the actual full radial trace.  This limit theorem
does not assume any radial-moment inequality or finite certificate. -/
theorem actualBoundaryRadialMoment_circle_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (p : ℝ) (hp : 0 ≤ p) :
    Tendsto
      (fun r : ℝ => Real.circleAverage (fun z : ℂ => ‖F z‖ ^ p) 0 r⁻¹)
      (𝓝[<] (1 : ℝ)) (𝓝 (actualBoundaryRadialMoment F p)) := by
  let μ : Measure ℝ := volume.restrict (Ioo (-Real.pi) Real.pi)
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    rw [Real.volume_Ioo]
    finiteness)
  have hnear : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r ∧ r < 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
    exact hr
  have hhalf : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 1 / 2 < r ∧ r < 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r hr
    exact hr
  have hmeas : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      AEStronglyMeasurable
        (fun θ : ℝ => ‖F (Complex.polarCoord.symm (r⁻¹, θ))‖ ^ p) μ := by
    filter_upwards [hnear] with r hr
    have hpcont : Continuous (fun θ : ℝ => Complex.polarCoord.symm (r⁻¹, θ)) := by
      simp_rw [Complex.polarCoord_symm_apply]
      fun_prop
    have hF := hc.1.continuousOn.comp_continuous hpcont (by
      intro θ
      change 1 < ‖Complex.polarCoord.symm (r⁻¹, θ)‖
      rw [Complex.norm_polarCoord_symm, abs_of_pos (inv_pos.2 hr.1)]
      exact (one_lt_inv₀ hr.1).2 hr.2)
    exact ((Real.continuous_rpow_const hp).comp hF.norm).aestronglyMeasurable
  have hbound : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      ∀ᵐ θ ∂μ, ‖‖F (Complex.polarCoord.symm (r⁻¹, θ))‖ ^ p‖ ≤ (3 : ℝ) ^ p := by
    filter_upwards [hhalf] with r hr
    have hr0 : 0 < r := by linarith [hr.1]
    have hi : r⁻¹ ≤ 2 := by
      calc
        r⁻¹ = 1 / r := (one_div r).symm
        _ ≤ 1 / (1 / 2 : ℝ) :=
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hr.1.le
        _ = 2 := by norm_num
    filter_upwards with θ
    have hF := exterior_polar_norm_le_radius_add_inv F hc hr0 hr.2 θ
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (by linarith [hr.2]) hp
  have hpoint : ∀ᵐ θ ∂μ,
      Tendsto (fun r : ℝ => ‖F (Complex.polarCoord.symm (r⁻¹, θ))‖ ^ p)
        (𝓝[<] (1 : ℝ)) (𝓝 (‖actualExteriorRadialTrace F θ‖ ^ p)) := by
    filter_upwards [actualExteriorRadialTrace_ae_tendsto F hc] with θ hθ
    exact (Real.continuous_rpow_const hp).continuousAt.tendsto.comp hθ.norm
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (fun _ : ℝ => (3 : ℝ) ^ p) hmeas hbound (integrable_const _) hpoint
  simpa only [circleAverage_eq_polar_setIntegral, actualBoundaryRadialMoment, μ]
    using hlim.const_mul ((2 * Real.pi)⁻¹)

end SpringerLean

#print axioms SpringerLean.actualBoundaryRadialMoment_circle_tendsto
