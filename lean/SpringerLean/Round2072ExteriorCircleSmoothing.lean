import SpringerLean.Round2071TruncatedExteriorPotential
import SpringerLean.Round2048AngularLogKernel

open Metric Set Real Filter

namespace SpringerLean

private theorem circleAverage_log_affine_exterior
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (x : ℂ) (r ε : ℝ) (hr : 1 < r) (hε : 0 < ε) :
    circleAverage (fun z => Real.log ‖(F z - x) / (ε : ℂ)‖) 0 r =
      circleAverage (fun z => Real.log ‖F z - x‖) 0 r - Real.log ε := by
  classical
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hε0 : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  have hsub : sphere (0 : ℂ) |r| ⊆ exteriorDisk := by
    intro z hz
    change 1 < ‖z‖
    have hn : ‖z‖ = r := by simpa [mem_sphere, dist_zero_right, abs_of_pos hr0] using hz
    rwa [hn]
  have ha : AnalyticOnNhd ℂ (fun z => F z - x) (sphere 0 |r|) :=
    fun z hz => (hF.1.analyticAt (exteriorDisk_isOpen.mem_nhds (hsub hz))).sub analyticAt_const
  rw [← circleAverage_const (Real.log ε) 0 r,
    ← circleAverage_fun_sub ha.meromorphicOn.circleIntegrable_log_norm
      (circleIntegrable_const _ _ _)]
  let excluded := if x ∈ F '' exteriorDisk then exteriorInverse F x else 0
  apply circleAverage_congr_codiscreteWithin _ hr0.ne'
  filter_upwards [self_mem_codiscreteWithin (sphere (0 : ℂ) |r|),
    compl_singleton_mem_codiscreteWithin excluded] with z hz hne
  have hnz : F z - x ≠ 0 := by
    intro heq
    have hzx := sub_eq_zero.mp heq
    have hx : x ∈ F '' exteriorDisk := ⟨z, hsub hz, hzx⟩
    have he := hF.2.1 (hsub hz) (Function.invFunOn_mem hx)
      (hzx.trans (Function.invFunOn_eq hx).symm)
    apply hne
    simpa [excluded, hx, exteriorInverse] using he
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  exact Real.log_div (norm_ne_zero_iff.mpr hnz) hε.ne'

private theorem log_max_eq_log_add_posLog (d ε : ℝ) (hd : 0 ≤ d) (hε : 0 < ε) :
    Real.log (max ε d) = Real.log ε + Real.posLog (d / ε) := by
  rw [Real.posLog_eq_log_max_one (div_nonneg hd hε.le),
    ← Real.log_mul hε.ne' (zero_lt_one.trans_le (le_max_left _ _)).ne',
    mul_max_of_nonneg _ _ hε.le, mul_one]
  have heq : ε * (d / ε) = d := by field_simp [hε.ne']
  rw [heq]

/-- Averaging the exterior-circle logarithmic potential over a circle
of test points replaces its logarithmic singularity by the exact
lower cutoff at that test circle's radius. -/
theorem exterior_circleAverage_log_potential_smoothing
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (x : ℂ) (r ε : ℝ) (hr : 1 < r) (hε : 0 < ε) :
    circleAverage (fun y => circleAverage (fun z => Real.log ‖F z - y‖) 0 r) x ε =
      circleAverage (fun z => Real.log (max ε ‖F z - x‖)) 0 r := by
  let g : ℝ → ℂ := fun θ => (F (circleMap 0 r θ) - x) / (ε : ℂ)
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hmem (θ : ℝ) : circleMap 0 r θ ∈ exteriorDisk := by
    change 1 < ‖circleMap 0 r θ‖
    simpa [norm_circleMap_zero, abs_of_pos hr0] using hr
  have hg : Continuous g := by
    exact ((hF.1.continuousOn.comp_continuous (continuous_circleMap _ _) hmem).sub
      continuous_const).div_const _
  have hswap := angular_integral_circle_log_potential g hg
  let P (u : ℂ) : ℝ :=
    circleAverage (fun z => Real.log ‖(F z - x) / (ε : ℂ) - u‖) 0 r
  have hP : circleAverage P 0 1 =
      circleAverage (fun z => Real.posLog (‖F z - x‖ / ε)) 0 r := by
    calc
      _ = (2 * π)⁻¹ * ((2 * π)⁻¹ *
          (∫ α in 0..2 * π, ∫ β in 0..2 * π,
            Real.log ‖g β - circleMap 0 1 α‖)) := by
        simp only [circleAverage_def, smul_eq_mul, P, g, intervalIntegral.integral_const_mul]
      _ = (2 * π)⁻¹ * (∫ β in 0..2 * π, Real.posLog ‖g β‖) := by
        rw [hswap]
        simp [← mul_assoc]
      _ = _ := by
        simp only [circleAverage_def, smul_eq_mul, g, norm_div, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hε]
  have hε0 : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  have hshift (u : ℂ) : P u =
      circleAverage (fun z => Real.log ‖F z - ((ε : ℂ) * u + x)‖) 0 r - Real.log ε := by
    unfold P
    simp_rw [show ∀ z : ℂ, (F z - x) / (ε : ℂ) - u =
      (F z - ((ε : ℂ) * u + x)) / (ε : ℂ) by
        intro z
        field_simp [hε0]
        ring]
    exact circleAverage_log_affine_exterior F hF _ r ε hr hε
  have hPint : CircleIntegrable P 0 1 := by
    simpa only [CircleIntegrable, circleAverage_def, smul_eq_mul, P, g] using
      (angular_circle_log_potential_outer_integrable g hg).const_mul ((2 * π)⁻¹)
  have hright : CircleIntegrable (fun z => Real.posLog (‖F z - x‖ / ε)) 0 r := by
    apply ContinuousOn.circleIntegrable'
    apply continuous_posLog.comp_continuousOn
    apply ContinuousOn.div_const
    apply ContinuousOn.norm
    apply ContinuousOn.sub _ continuousOn_const
    apply hF.1.continuousOn.mono
    intro z hz
    change 1 < ‖z‖
    rwa [show ‖z‖ = r by simpa [mem_sphere, dist_zero_right, abs_of_pos hr0] using hz]
  rw [circleAverage_eq_circleAverage_zero_one]
  have hs (u : ℂ) :
      circleAverage (fun z => Real.log ‖F z - ((ε : ℂ) * u + x)‖) 0 r =
        P u + Real.log ε := by rw [hshift]; ring
  simp_rw [hs]
  rw [circleAverage_fun_add hPint (circleIntegrable_const _ _ _), circleAverage_const, hP]
  simp_rw [log_max_eq_log_add_posLog _ ε (norm_nonneg _) hε]
  rw [circleAverage_fun_add (circleIntegrable_const _ _ _) hright, circleAverage_const, add_comm]

end SpringerLean
