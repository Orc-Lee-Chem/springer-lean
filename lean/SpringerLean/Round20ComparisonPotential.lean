import SpringerLean.Round20JensenLower

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The comparison line-segment logarithmic potential is nonnegative at
every complex target. The analytic polynomial `1 - z u + u²` has center
value one; its norm on the unit circle is the comparison distance. -/
theorem comparisonCircle_boundary_log_potential_nonneg (z : ℂ) :
    0 ≤ Real.circleAverage
      (fun ζ : ℂ => Real.log ‖z - ((2 * ζ.re : ℝ) : ℂ)‖) 0 1 := by
  let q : ℂ → ℂ := fun u => 1 - z * u + u ^ 2
  have hq : AnalyticOnNhd ℂ q (closedBall (0 : ℂ) 1) := by
    intro u hu
    dsimp [q]
    fun_prop
  have hq0 : q 0 ≠ 0 := by
    simp [q]
  have hJ := analytic_circleAverage_log_norm_ge_center q hq hq0
  have hqcenter : Real.log ‖q 0‖ = 0 := by simp [q]
  rw [hqcenter] at hJ
  calc
    0 ≤ Real.circleAverage (fun ζ : ℂ => Real.log ‖q ζ‖) 0 1 := hJ
    _ = Real.circleAverage
        (fun ζ : ℂ => Real.log ‖z - ((2 * ζ.re : ℝ) : ℂ)‖) 0 1 := by
          apply Real.circleAverage_congr_sphere
          intro ζ hζ
          apply congrArg Real.log
          have hnorm : ‖ζ‖ = 1 := by
            simpa only [mem_sphere, dist_zero_right, abs_one] using hζ
          have hmul : ζ * conj ζ = 1 := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
            norm_num
          have hfactor : q ζ = ζ * (((2 * ζ.re : ℝ) : ℂ) - z) := by
            dsimp [q]
            rw [← Complex.add_conj]
            linear_combination -hmul
          rw [hfactor, norm_mul, hnorm, one_mul, norm_sub_rev]

end SpringerLean
