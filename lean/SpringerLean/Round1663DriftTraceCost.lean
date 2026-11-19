import SpringerLean.Round1652ActualAntiholomorphicCost

namespace SpringerLean

/-- The real trace of the antiholomorphic drift has no larger cost
than the norm of the derivative times the squared normalized phase. -/
theorem phase_drift_trace_cost_le
    (H c : ℂ) (hH : H ≠ 0) (U : ℝ) :
    U^2 * (c/H^2).re ≤ ‖c‖ * (U/‖H‖)^2 := by
  have hy : 0 < ‖H‖ := norm_pos_iff.mpr hH
  have hc : (c/H^2).re ≤ ‖c/H^2‖ :=
    le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg U)
  rw [norm_div, norm_pow] at hm
  convert hm using 1 <;> field_simp

end SpringerLean

#print axioms SpringerLean.phase_drift_trace_cost_le
