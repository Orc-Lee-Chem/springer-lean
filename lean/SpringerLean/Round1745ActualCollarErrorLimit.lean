import SpringerLean.Round1744ActualFluxMeasurable
import SpringerLean.Round1742RadialEnergyCutoff
import SpringerLean.Round1743CutoffEnergyLimit

open MeasureTheory Filter Metric
open scoped Topology ComplexConjugate

namespace SpringerLean

noncomputable def actualEnergyCutoffError
    (F : ℂ → ℂ) (k : ℕ) (beta : ℂ) (ε : ℝ) (z : ℂ) : ℝ :=
  (fderiv ℝ (radialEnergyCutoff ε) z) (actualEnergyFluxField F k beta z)

/-- Both radial boundary errors are dominated by one L1 function,
uniformly in the cutoff width. -/
theorem actualEnergyCutoffError_common_majorant
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ z : ℂ, ‖z‖ < 1 →
      |actualEnergyCutoffError F k beta ε z| ≤
        C * (1 + ‖deriv (exteriorForwardGerm F) (conj z)‖) := by
  obtain ⟨C, hC, hJ⟩ :=
    actualEnergyFluxField_norm_le_boundary_distance F hc k hk beta hbeta
  refine ⟨4*C, by positivity, ?_⟩
  intro ε hε z hz
  by_cases hcore : 2*ε < ‖z‖ ∧ ‖z‖ < 1-2*ε
  · have hzero := radialEnergyCutoff_fderiv_zero_core hε hcore.1 hcore.2
    simp only [actualEnergyCutoffError, hzero, ContinuousLinearMap.zero_apply,
      abs_zero]
    positivity
  · have hmin : min ‖z‖ (1-‖z‖) ≤ 2*ε := by
      by_cases hi : 2*ε < ‖z‖
      · have ho : 1-2*ε ≤ ‖z‖ := le_of_not_gt (fun ho => hcore ⟨hi, ho⟩)
        exact (min_le_right _ _).trans (by linarith)
      · exact (min_le_left _ _).trans (le_of_not_gt hi)
    have hraw := (fderiv ℝ (radialEnergyCutoff ε) z).le_opNorm
      (actualEnergyFluxField F k beta z)
    rw [Real.norm_eq_abs] at hraw
    calc
      _ ≤ _ := hraw
      _ ≤ (2/ε) * (C * min ‖z‖ (1-‖z‖) *
          (1 + ‖deriv (exteriorForwardGerm F) (conj z)‖)) :=
        mul_le_mul (radialEnergyCutoff_fderiv_norm_le hε z)
          (hJ z hz) (norm_nonneg _) (by positivity)
      _ ≤ (2/ε) * (C * (2*ε) *
          (1 + ‖deriv (exteriorForwardGerm F) (conj z)‖)) := by gcongr
      _ = _ := by field_simp; ring

/-- The actual inner and outer collar integrals tend to zero. No
unweighted-divergence integrability assumption is made here. -/
theorem actualEnergyCutoffError_integral_tendsto_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => ∫ z in ball (0 : ℂ) 1,
      actualEnergyCutoffError F k beta (ε j) z ∂volume)
      atTop (𝓝 0) := by
  let μ : Measure ℂ := volume.restrict (ball (0 : ℂ) 1)
  obtain ⟨C, hC, hbound⟩ :=
    actualEnergyCutoffError_common_majorant F hc k hk beta hbeta
  have hmeas (j : ℕ) : AEStronglyMeasurable
      (actualEnergyCutoffError F k beta (ε j)) μ := by
    have hL : AEMeasurable (fderiv ℝ (radialEnergyCutoff (ε j))) μ :=
      (measurable_fderiv ℝ _).aemeasurable
    have hJ := (actualEnergyFluxField_aestronglyMeasurable_unitDisk
      F hc k beta).aemeasurable
    have happ : Continuous (fun p : (ℂ →L[ℝ] ℝ) × ℂ => p.1 p.2) := by fun_prop
    exact (happ.measurable.comp_aemeasurable (hL.prodMk hJ)).aestronglyMeasurable
  have hmajor : Integrable (fun z : ℂ =>
      C*(1 + ‖deriv (exteriorForwardGerm F) (conj z)‖)) μ :=
    (actualForwardDerivative_boundaryMajorant_integrableOn F hc).const_mul C
  have hdom (j : ℕ) : ∀ᵐ z ∂μ,
      ‖actualEnergyCutoffError F k beta (ε j) z‖ ≤
        C*(1 + ‖deriv (exteriorForwardGerm F) (conj z)‖) := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    rw [Real.norm_eq_abs]
    exact hbound (ε j) (hε j) z (by simpa only [Metric.mem_ball,
      dist_zero_right] using hz)
  have hae0 : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
    apply ae_iff.mpr
    simp
  have hpt : ∀ᵐ z ∂μ,
      Tendsto (fun j => actualEnergyCutoffError F k beta (ε j) z)
        atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_of_ae hae0,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz0 hz
    have hz' : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hevent := radialEnergyCutoff_eventually_fderiv_zero ε hε hlim hz0 hz'
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with j hj
    simp [actualEnergyCutoffError, hj]
  have h := tendsto_integral_of_dominated_convergence _ hmeas hmajor hdom hpt
  simpa using h

end SpringerLean

#print axioms SpringerLean.actualEnergyCutoffError_integral_tendsto_zero
