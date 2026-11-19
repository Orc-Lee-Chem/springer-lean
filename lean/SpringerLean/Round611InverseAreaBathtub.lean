import SpringerLean.Round608EqualAreaExchange
import SpringerLean.Round610BallInversionIntegral

open MeasureTheory Filter
open scoped ENNReal

namespace SpringerLean
set_option Elab.async false

/-- Among finite-area omitted sets, the centered disk minimizes the
inverse-fourth-power complementary integral. The integrability hypothesis
excludes the default value of an ordinary nonintegrable integral. -/
theorem planar_inverse_fourth_complement_lower
    (K : Set ℂ) (hK : MeasurableSet K) (hKfin : volume K ≠ ∞)
    (hKpos : 0 < volume.real K)
    (hf : IntegrableOn (fun z : ℂ => ‖z‖⁻¹ ^ 4) Kᶜ) :
    Real.pi ^ 2 / volume.real K ≤ ∫ z in Kᶜ, ‖z‖⁻¹ ^ 4 := by
  let r := Real.sqrt (volume.real K / Real.pi)
  have ha : 0 < volume.real K / Real.pi := div_pos hKpos Real.pi_pos
  have hr : 0 < r := Real.sqrt_pos.mpr ha
  have hrsq : r ^ 2 = volume.real K / Real.pi := Real.sq_sqrt ha.le
  have hBfin : volume (Metric.ball (0 : ℂ) r) ≠ ∞ := by
    rw [Complex.volume_ball]
    finiteness
  have harea : volume.real (Metric.ball (0 : ℂ) r) = volume.real K := by
    have hv : volume.real (Metric.ball (0 : ℂ) r) = r ^ 2 * Real.pi := by
      simp [measureReal_def, Complex.volume_ball, hr.le]
    rw [hv, hrsq]
    field_simp [Real.pi_ne_zero]
  have hzero : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := volume.ae_ne 0
  have hinside : ∀ᵐ z : ℂ ∂volume,
      z ∈ Metric.ball (0 : ℂ) r \ K → r⁻¹ ^ 4 ≤ ‖z‖⁻¹ ^ 4 := by
    filter_upwards [hzero] with z hz hzB
    have hzn : ‖z‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hzB.1
    have hn : r⁻¹ ≤ ‖z‖⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (norm_pos_iff.mpr hz) hzn.le
    exact pow_le_pow_left₀ (inv_nonneg.mpr hr.le) hn 4
  have houtside : ∀ᵐ z : ℂ ∂volume,
      z ∈ K \ Metric.ball (0 : ℂ) r → ‖z‖⁻¹ ^ 4 ≤ r⁻¹ ^ 4 := by
    filter_upwards [] with z hzB
    have hzn : r ≤ ‖z‖ := by
      simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hzB.2
    have hn : ‖z‖⁻¹ ≤ r⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hr hzn
    exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hn 4
  obtain ⟨hiB,hval⟩ := inverse_fourth_integral_ball_compl hr
  have he := equal_area_complement_integral_le volume (Metric.ball (0 : ℂ) r) K
    Metric.isOpen_ball.measurableSet hK hBfin hKfin harea
    (fun z : ℂ => ‖z‖⁻¹ ^ 4) (r⁻¹ ^ 4) hiB hf hinside houtside
  rw [hval] at he
  have hconst : Real.pi / r ^ 2 = Real.pi ^ 2 / volume.real K := by
    rw [hrsq]
    field_simp [Real.pi_ne_zero, ne_of_gt hKpos]
  rwa [hconst] at he

end SpringerLean
