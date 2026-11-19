import SpringerLean.Round28ComparisonHorizontalUniform

open MeasureTheory Set

namespace SpringerLean

/-- The comparison-potential integral vanishes continuously as the
centered interval collapses to zero, even when negative heights are allowed. -/
theorem comparisonSegmentPotential_interval_integral_continuousAt_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a : ℝ) :
    ContinuousAt
      (fun u : ℝ => ∫ t in Icc (-u) u,
        comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I)) 0 := by
  let f : ℝ → ℝ := fun t => comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I)
  have hf (b c : ℝ) : IntervalIntegrable f volume b c :=
    comparisonSegmentPotential_vertical_intervalIntegrable
      F hc hs0 hs1 ξ hξ a b c
  let P : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, f t
  have hP : Continuous P := intervalIntegral.continuous_primitive hf 0
  have hEqPos (u : ℝ) (hu : 0 ≤ u) :
      (∫ t in Icc (-u) u, f t) = P u - P (-u) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -u ≤ u)]
    exact (intervalIntegral.integral_interval_sub_left (hf 0 u) (hf 0 (-u))).symm
  have hEq (u : ℝ) :
      (∫ t in Icc (-u) u, f t) = P (max u 0) - P (-(max u 0)) := by
    by_cases hu : 0 ≤ u
    · rw [max_eq_left hu]
      exact hEqPos u hu
    · have hlt : u < 0 := lt_of_not_ge hu
      rw [Icc_eq_empty_of_lt (by linarith : u < -u)]
      simp [max_eq_right (le_of_lt hlt)]
  have hcont : ContinuousAt (fun u : ℝ => P (max u 0) - P (-(max u 0))) 0 := by
    fun_prop
  convert hcont using 1
  funext u
  exact hEq u
end SpringerLean