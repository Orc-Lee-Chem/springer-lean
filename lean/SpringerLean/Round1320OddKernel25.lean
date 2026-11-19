import SpringerLean.Round620StripLogKernel
import Mathlib.Analysis.Complex.Exponential

namespace SpringerLean

noncomputable def largeRootRadius : ℝ := Real.sqrt (25/24 : ℝ)

theorem largeRootRadius_sq : largeRootRadius ^ 2 = (25/24 : ℝ) := by
  exact Real.sq_sqrt (by norm_num)

theorem largeRootRadius_gt_one : 1 < largeRootRadius := by
  have hs := largeRootRadius_sq
  have hn : 0 ≤ largeRootRadius := Real.sqrt_nonneg _
  nlinarith

theorem largeRootRadius_le_25_24 : largeRootRadius ≤ (25/24 : ℝ) := by
  have hs := largeRootRadius_sq
  have hr := largeRootRadius_gt_one
  nlinarith

/-- Seven positive Taylor terms suffice for the logarithmic kernel. -/
theorem log_seven_lt_49_25 : Real.log 7 < (49/25 : ℝ) := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 7)).2
  have hsum : (7 : ℝ) <
      ∑ j ∈ Finset.range 7, (49/25 : ℝ)^j / (j.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 7)

theorem largeRootRadius_kernel_eq :
    exteriorStripLogKernel largeRootRadius = Real.log 7 - 24/25 := by
  unfold exteriorStripLogKernel
  rw [largeRootRadius_sq]
  have hratio : ((25/24 : ℝ)+1)/((25/24 : ℝ)-1) = 49 := by norm_num
  rw [hratio]
  have hlog : Real.log (49 : ℝ) / 2 = Real.log 7 := by
    have h := Real.log_pow (7 : ℝ) 2
    norm_num at h ⊢
    linarith
  rw [hlog]
  norm_num

theorem largeRootRadius_kernel_lt_one :
    exteriorStripLogKernel largeRootRadius < 1 := by
  rw [largeRootRadius_kernel_eq]
  linarith [log_seven_lt_49_25]

end SpringerLean
