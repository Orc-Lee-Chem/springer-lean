import SpringerLean.Round29ActualReferenceFar

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- A global linear upper bound for the comparison segment potential,
valid also at the segment's logarithmic singularities. -/
theorem comparisonSegmentPotential_le_norm_add_two (z : ℂ) :
    comparisonSegmentPotential z ≤ ‖z‖ + 2 := by
  let q : ℂ → ℂ := fun u => 1 - z * u + u ^ 2
  have hq : AnalyticOnNhd ℂ q (closedBall (0 : ℂ) 1) := by
    intro u hu
    dsimp [q]
    fun_prop
  have hqs : AnalyticOnNhd ℂ q (sphere (0:ℂ) |(1:ℝ)|) := by
    simpa only [abs_one] using hq.mono sphere_subset_closedBall
  have hci : CircleIntegrable (fun ζ : ℂ => Real.log ‖q ζ‖) 0 1 :=
    hqs.meromorphicOn.circleIntegrable_log_norm
  have hqb (ζ : ℂ) (hζ : ζ ∈ sphere (0:ℂ) 1) :
      Real.log ‖q ζ‖ ≤ ‖z‖ + 2 := by
    have hnorm : ‖ζ‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hζ
    have htri : ‖(1:ℂ) - z * ζ‖ ≤ 1 + ‖z‖ := by
      calc
        ‖(1:ℂ) - z * ζ‖ ≤ ‖(1:ℂ)‖ + ‖z * ζ‖ := norm_sub_le _ _
        _ = 1 + ‖z‖ := by simp [norm_mul, hnorm]
    have hqnorm : ‖q ζ‖ ≤ ‖z‖ + 2 := by
      calc
        ‖q ζ‖ ≤ ‖(1:ℂ) - z * ζ‖ + ‖ζ ^ 2‖ := by
          dsimp [q]
          exact norm_add_le _ _
        _ ≤ ‖z‖ + 2 := by rw [norm_pow, hnorm]; linarith
    exact (Real.log_le_self (norm_nonneg _)).trans hqnorm
  have hqavg : Real.circleAverage (fun ζ : ℂ => Real.log ‖q ζ‖) 0 1 ≤
      ‖z‖ + 2 := Real.circleAverage_mono_on_of_le_circle hci (by
        intro ζ hζ
        exact hqb ζ (by simpa only [abs_one] using hζ))
  have hEq : Real.circleAverage (fun ζ : ℂ => Real.log ‖q ζ‖) 0 1 =
      comparisonSegmentPotential z := by
    dsimp [comparisonSegmentPotential]
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
  rw [hEq] at hqavg
  exact hqavg
end SpringerLean