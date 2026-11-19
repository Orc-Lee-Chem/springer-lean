import SpringerLean.Round1847ActualExteriorTrace
import SpringerLean.Round1334CoefficientRadialLimit

open MeasureTheory Filter Set
open scoped Topology

namespace SpringerLean

theorem circleMap_eq_polar_radius (r θ : ℝ) :
    circleMap 0 r θ = Complex.polarCoord.symm (r, θ) := by
  rw [circleMap_zero, Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- The normalization is circle length 2π, not normalized disk area. -/
theorem circleAverage_eq_polar_setIntegral (f : ℂ → ℝ) (r : ℝ) :
    Real.circleAverage f 0 r = (2 * Real.pi)⁻¹ *
      ∫ θ in Ioo (-Real.pi) Real.pi, f (Complex.polarCoord.symm (r, θ)) := by
  rw [Real.circleAverage_eq_integral_add (-Real.pi)]
  rw [intervalIntegral.integral_comp_add_right
    (fun θ : ℝ => f (circleMap 0 r θ)) (-Real.pi)]
  have he : 2 * Real.pi + -Real.pi = Real.pi := by ring
  rw [zero_add, he, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo]
  simp only [smul_eq_mul, circleMap_eq_polar_radius]

/-- Moments of the actual a.e. radial trace.  The preceding theorem
identifies this representative with the original exterior map along all
radial approaches outside an angular null set. -/
noncomputable def actualBoundaryRadialMoment (F : ℂ → ℂ) (p : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    ∫ θ in Ioo (-Real.pi) Real.pi, ‖actualExteriorRadialTrace F θ‖ ^ p

/-- Actual boundary Parseval.  This closes the passage from exterior
circles to the original map's radial trace, rather than just defining
the moment by its coefficient series. -/
theorem actualBoundaryRadialMoment_two_eq_coeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 2 =
      1 + ∑' j : ℕ, ‖exteriorForwardCoeff F j‖ ^ 2 := by
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
        (fun θ : ℝ => ‖F (Complex.polarCoord.symm (r⁻¹, θ))‖ ^ 2) μ := by
    filter_upwards [hnear] with r hr
    have hp : Continuous (fun θ : ℝ => Complex.polarCoord.symm (r⁻¹, θ)) := by
      simp_rw [Complex.polarCoord_symm_apply]
      fun_prop
    have hF := hc.1.continuousOn.comp_continuous hp (by
      intro θ
      change 1 < ‖Complex.polarCoord.symm (r⁻¹, θ)‖
      rw [Complex.norm_polarCoord_symm, abs_of_pos (inv_pos.2 hr.1)]
      exact (one_lt_inv₀ hr.1).2 hr.2)
    exact (hF.norm.pow 2).aestronglyMeasurable
  have hbound : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      ∀ᵐ θ ∂μ, ‖‖F (Complex.polarCoord.symm (r⁻¹, θ))‖ ^ 2‖ ≤ (9 : ℝ) := by
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
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (F (Complex.polarCoord.symm (r⁻¹, θ)))]
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (fun _ : ℝ => (9 : ℝ)) hmeas hbound (integrable_const _)
    ((actualExteriorRadialTrace_ae_tendsto F hc).mono (fun _ h => h.norm.pow 2))
  have hactual : Tendsto
      (fun r : ℝ => Real.circleAverage (fun z : ℂ => ‖F z‖ ^ 2) 0 r⁻¹)
      (𝓝[<] (1 : ℝ)) (𝓝 (actualBoundaryRadialMoment F 2)) := by
    simpa only [circleAverage_eq_polar_setIntegral, actualBoundaryRadialMoment,
      Real.rpow_two, μ] using hlim.const_mul ((2 * Real.pi)⁻¹)
  have hcoeff := exterior_actual_circle_two_energy_tendsto_boundary_coeff F hc hnear
    (show Tendsto (fun r : ℝ => r) (𝓝[<] (1 : ℝ)) (𝓝 1) from nhdsWithin_le_nhds)
  exact tendsto_nhds_unique hactual hcoeff

theorem actualBoundaryRadialMoment_two_margin
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 2 ≤
      2 * (1 - (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 4) := by
  rw [actualBoundaryRadialMoment_two_eq_coeff F hc]
  exact exteriorForwardCoeff_tsum_radial_two_margin F hc

end SpringerLean

#print axioms SpringerLean.actualBoundaryRadialMoment_two_eq_coeff
#print axioms SpringerLean.actualBoundaryRadialMoment_two_margin
