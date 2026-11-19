import SpringerLean.Round1911ProjectionPhaseCircle
import SpringerLean.Round1848ActualBoundaryParseval

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace SpringerLean

noncomputable def actualBoundaryProjectionSecondMoment
    (F : ℂ → ℂ) (c : ℂ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    ∫ θ in Ioo (-Real.pi) Real.pi,
      ((c * actualExteriorRadialTrace F θ).re / 2) ^ 2

/-- The smooth harmonic filling has the same quadratic projection moment
as the actual almost-everywhere radial trace at the unit boundary. -/
theorem actualHarmonic_projection_square_tendsto_trace
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (c : ℂ) (hcunit : ‖c‖ = 1) :
    Tendsto
      (fun r : ℝ => Real.circleAverage
        (fun z : ℂ => ((c * actualHarmonic F z).re / 2) ^ 2) 0 r)
      (𝓝[<] (1 : ℝ))
      (𝓝 (actualBoundaryProjectionSecondMoment F c)) := by
  let μ : Measure ℝ := volume.restrict (Ioo (-Real.pi) Real.pi)
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    rw [Real.volume_Ioo]
    finiteness)
  have hnear : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r ∧ r < 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
    exact hr
  have hmeas : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      AEStronglyMeasurable
        (fun θ : ℝ =>
          ((c * actualHarmonic F (Complex.polarCoord.symm (r, θ))).re / 2) ^ 2)
        μ := by
    filter_upwards [hnear] with r hr
    have hp : Continuous (fun θ : ℝ => Complex.polarCoord.symm (r, θ)) := by
      simp_rw [Complex.polarCoord_symm_apply]
      fun_prop
    have hF := (actualHarmonic_continuousOn_unitBall F hc).comp_continuous
      hp (by
        intro θ
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
          abs_of_pos hr.1]
        exact hr.2)
    exact (((Complex.continuous_re.comp (continuous_const.mul hF)).div_const 2).pow 2).aestronglyMeasurable
  have hbound : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      ∀ᵐ θ : ℝ ∂μ,
        ‖((c * actualHarmonic F (Complex.polarCoord.symm (r, θ))).re / 2) ^ 2‖ ≤
          (1 : ℝ) := by
    filter_upwards [hnear] with r hr
    filter_upwards with θ
    have hz : ‖Complex.polarCoord.symm (r, θ)‖ < 1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr.1]
      exact hr.2
    have hH := actualHarmonic_norm_le_two_norm F hc hz
    have hRe : |(c * actualHarmonic F (Complex.polarCoord.symm (r, θ))).re / 2| ≤ 1 := by
      calc
        _ = |(c * actualHarmonic F (Complex.polarCoord.symm (r, θ))).re| / 2 := by
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        _ ≤ ‖c * actualHarmonic F (Complex.polarCoord.symm (r, θ))‖ / 2 :=
          div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (by norm_num)
        _ ≤ 1 := by
          rw [norm_mul, hcunit, one_mul, Complex.norm_polarCoord_symm,
            abs_of_pos hr.1] at *
          linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rcases abs_le.mp hRe with ⟨hlo, hhi⟩
    nlinarith
  have hpoint : ∀ᵐ θ : ℝ ∂μ,
      Tendsto
        (fun r : ℝ =>
          ((c * actualHarmonic F (Complex.polarCoord.symm (r, θ))).re / 2) ^ 2)
        (𝓝[<] (1 : ℝ))
        (𝓝 (((c * actualExteriorRadialTrace F θ).re / 2) ^ 2)) := by
    filter_upwards [exteriorForwardGerm_ae_conjugate_radial_limit F hc] with θ hθ
    have hr : Tendsto (fun r : ℝ => Complex.polarCoord.symm (r, θ))
        (𝓝[<] (1 : ℝ)) (𝓝 (Complex.polarCoord.symm (1, θ))) := by
      have hcont : Continuous (fun r : ℝ => Complex.polarCoord.symm (r, θ)) := by
        simp_rw [Complex.polarCoord_symm_apply]
        fun_prop
      exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hH : Tendsto
        (fun r : ℝ => actualHarmonic F (Complex.polarCoord.symm (r, θ)))
        (𝓝[<] (1 : ℝ)) (𝓝 (actualExteriorRadialTrace F θ)) := by
      simpa only [actualHarmonic, actualExteriorRadialTrace] using hr.add hθ
    have hcont : Continuous (fun z : ℂ => ((c * z).re / 2) ^ 2) := by
      fun_prop
    exact hcont.continuousAt.tendsto.comp hH
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (fun _ : ℝ => (1 : ℝ)) hmeas hbound (integrable_const _) hpoint
  simpa only [circleAverage_eq_polar_setIntegral,
    actualBoundaryProjectionSecondMoment, μ] using
      hlim.const_mul ((2 * Real.pi)⁻¹)

end SpringerLean

#print axioms SpringerLean.actualHarmonic_projection_square_tendsto_trace
