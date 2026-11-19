import SpringerLean.Round609InversionArea
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory Filter
open scoped ENNReal

namespace SpringerLean
set_option Elab.async false

theorem inversion_image_ball_compl {r : ℝ} (hr : 0 < r) :
    (fun z : ℂ => z⁻¹) '' (Metric.ball (0 : ℂ) r)ᶜ =
      Metric.closedBall (0 : ℂ) r⁻¹ \ {0} := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    have hzr : r ≤ ‖z‖ := by
      simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hz
    have hz0 : z ≠ 0 := by intro he; simp [he] at hzr; linarith
    have hn : ‖z⁻¹‖ ≤ r⁻¹ := by
      rw [norm_inv]
      simpa only [one_div] using one_div_le_one_div_of_le hr hzr
    exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hn,
      by simpa only [Set.mem_singleton_iff] using inv_ne_zero hz0⟩
  · rintro ⟨hy,hy0⟩
    have hyz : y ≠ 0 := by simpa only [Set.mem_singleton_iff] using hy0
    have hyn : ‖y‖ ≤ r⁻¹ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
    have hn : r ≤ ‖y⁻¹‖ := by
      rw [norm_inv]
      simpa only [one_div, inv_inv] using
        one_div_le_one_div_of_le (norm_pos_iff.mpr hyz) hyn
    refine ⟨y⁻¹, ?_, by simp⟩
    simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hn

theorem inverse_fourth_lintegral_ball_compl {r : ℝ} (hr : 0 < r) :
    (∫⁻ z in (Metric.ball (0 : ℂ) r)ᶜ, ENNReal.ofReal (‖z‖⁻¹ ^ 4)) =
      ENNReal.ofReal r⁻¹ ^ 2 * NNReal.pi := by
  have hzero : (0 : ℂ) ∉ (Metric.ball (0 : ℂ) r)ᶜ := by simp [hr]
  rw [inversion_image_volume_eq_lintegral _ Metric.isOpen_ball.measurableSet.compl hzero,
    inversion_image_ball_compl hr]
  have hnull : volume (Metric.closedBall (0 : ℂ) r⁻¹ ∩ ({0} : Set ℂ)) = 0 :=
    measure_mono_null Set.inter_subset_right (by simp)
  rw [measure_sdiff_null' hnull, Complex.volume_closedBall]

theorem inverse_fourth_integral_ball_compl {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun z : ℂ => ‖z‖⁻¹ ^ 4) (Metric.ball (0 : ℂ) r)ᶜ ∧
      (∫ z in (Metric.ball (0 : ℂ) r)ᶜ, ‖z‖⁻¹ ^ 4) = Real.pi / r ^ 2 := by
  have hm : Measurable (fun z : ℂ => ‖z‖⁻¹ ^ 4) := by fun_prop
  have hn : ∀ z : ℂ, 0 ≤ ‖z‖⁻¹ ^ 4 := by intro z; positivity
  have hi : IntegrableOn (fun z : ℂ => ‖z‖⁻¹ ^ 4) (Metric.ball (0 : ℂ) r)ᶜ := by
    refine ⟨hm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).mpr ?_⟩
    rw [inverse_fourth_lintegral_ball_compl hr]
    finiteness
  have he := inverse_fourth_lintegral_ball_compl hr
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)] at he
  have hh := congrArg ENNReal.toReal he
  have hp : 0 ≤ ∫ z in (Metric.ball (0 : ℂ) r)ᶜ, ‖z‖⁻¹ ^ 4 := integral_nonneg hn
  have hri : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  rw [ENNReal.toReal_ofReal hp] at hh
  refine ⟨hi, ?_⟩
  simpa [hri, div_eq_mul_inv, inv_pow, mul_comm] using hh

end SpringerLean
