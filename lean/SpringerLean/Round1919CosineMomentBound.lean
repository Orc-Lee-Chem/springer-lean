import SpringerLean.Round1918NormalizedEvenDeficits

open Metric

namespace SpringerLean

theorem normalizedCosineMoment_two : normalizedCosineMoment 2 = 1 / 2 := by
  rw [normalizedCosineMoment_eq_slit_constant 2 (by norm_num),
    slitRadialMomentConstant_two]
  norm_num

theorem normalizedCosineMoment_nonneg (p : ℝ) :
    0 ≤ normalizedCosineMoment p := by
  unfold normalizedCosineMoment
  apply Real.circleAverage_nonneg_of_nonneg
  intro z hz
  exact Real.rpow_nonneg (abs_nonneg _) _

theorem normalizedCosineMoment_le_half
    (p : ℝ) (hp : 2 ≤ p) :
    normalizedCosineMoment p ≤ 1 / 2 := by
  have hcontp : Continuous (fun z : ℂ => |z.re| ^ p) := by
    have h := Real.continuous_rpow_const (by linarith : 0 ≤ p)
    fun_prop
  have hcont2 : Continuous (fun z : ℂ => |z.re| ^ (2 : ℝ)) := by
    have h := Real.continuous_rpow_const (by norm_num : 0 ≤ (2 : ℝ))
    fun_prop
  have hcmp : Real.circleAverage (fun z : ℂ => |z.re| ^ p) 0 1 ≤
      Real.circleAverage (fun z : ℂ => |z.re| ^ (2 : ℝ)) 0 1 := by
    apply Real.circleAverage_mono
      (hcontp.continuousOn.circleIntegrable (by norm_num))
      (hcont2.continuousOn.circleIntegrable (by norm_num))
    intro z hz
    have hnorm : ‖z‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right, abs_one] using hz
    have hle : |z.re| ≤ 1 := by
      simpa only [hnorm] using Complex.abs_re_le_norm z
    exact Real.rpow_le_rpow_of_exponent_ge'
      (abs_nonneg _) hle (by norm_num) hp
  change normalizedCosineMoment p ≤ normalizedCosineMoment 2 at hcmp
  rwa [normalizedCosineMoment_two] at hcmp

end SpringerLean

#print axioms SpringerLean.normalizedCosineMoment_le_half
