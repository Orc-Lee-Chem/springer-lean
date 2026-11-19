import SpringerLean.Round29ReferenceKernel
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace SpringerLean

/-- The logarithmic point kernel has a quadratic remainder once the
source is at most half as far from zero as the target. -/
theorem log_norm_sub_quadratic_remainder
    (z w : ℂ) (hz : z ≠ 0) (hw : ‖w / z‖ ≤ (1 / 2 : ℝ)) :
    |Real.log ‖z - w‖ - Real.log ‖z‖ + (w / z).re| ≤ ‖w / z‖ ^ 2 := by
  let u : ℂ := -(w / z)
  have hu : ‖u‖ ≤ (1 / 2 : ℝ) := by simpa [u] using hw
  have hu1 : ‖u‖ < 1 := by linarith
  have hu0 : 0 < 1 - ‖u‖ := by linarith
  have hnonzero : (1 : ℂ) + u ≠ 0 := by
    intro heq
    have hueq : u = -1 := by linear_combination heq
    have : ‖u‖ = 1 := by simp [hueq]
    linarith
  have hfactor : z - w = z * (1 + u) := by
    dsimp [u]
    field_simp [hz]
    ring
  have hlog : Real.log ‖z - w‖ = Real.log ‖z‖ + Real.log ‖1 + u‖ := by
    rw [hfactor, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hz)
      (norm_ne_zero_iff.mpr hnonzero)]
  have hre : Real.log ‖z - w‖ - Real.log ‖z‖ + (w / z).re =
      (Complex.log (1 + u) - u).re := by
    rw [hlog, Complex.sub_re, Complex.log_re]
    dsimp [u]
    simp
  rw [hre]
  have hquad := Complex.norm_log_one_add_sub_self_le hu1
  have hinv : (1 - ‖u‖)⁻¹ ≤ (2 : ℝ) := by
    apply (inv_le_comm₀ hu0 (by norm_num : (0:ℝ)<2)).2
    linarith
  have hquad' : ‖Complex.log (1 + u) - u‖ ≤ ‖u‖ ^ 2 := by
    have hmult := mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖u‖)
    nlinarith
  exact (Complex.abs_re_le_norm _).trans (by simpa [u] using hquad')

/-- A far source has a quadratic logarithm error after its linear term. -/
theorem log_norm_sub_far_quadratic
    (z w : ℂ) (hz : z ≠ 0) (hfar : 2 * ‖w‖ ≤ ‖z‖) :
    |Real.log ‖z - w‖ - Real.log ‖z‖ + (w / z).re| ≤
      ‖w‖ ^ 2 / ‖z‖ ^ 2 := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hratio : ‖w / z‖ ≤ (1 / 2 : ℝ) := by
    rw [norm_div]
    apply (div_le_iff₀ hzpos).2
    linarith
  simpa only [norm_div, div_pow] using
    log_norm_sub_quadratic_remainder z w hz hratio
end SpringerLean