import SpringerLean.Round27CostComparison

open MeasureTheory Metric
open scoped Real

namespace SpringerLean

/-- The logarithmic kernel has the circular submean inequality away from
its pole. The explicit `z ≠ w` matters because Lean defines `log 0 = 0`,
whereas the analytic kernel has a negative infinite singularity there. -/
theorem log_norm_sub_le_circleAverage_of_ne
    (z w : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hzw : z ≠ w) :
    Real.log ‖z - w‖ ≤
      Real.circleAverage (fun u : ℂ => Real.log ‖u - w‖) z ρ := by
  have hd : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  have hquot : 0 < ρ⁻¹ * ‖z - w‖ := mul_pos (inv_pos.mpr hρ) hd
  have hfactor : ρ * (ρ⁻¹ * ‖z - w‖) = ‖z - w‖ := by
    field_simp
  have hlog : Real.log ‖z - w‖ =
      Real.log ρ + Real.log (ρ⁻¹ * ‖z - w‖) := by
    rw [← Real.log_mul (ne_of_gt hρ) (ne_of_gt hquot), hfactor]
  calc
    Real.log ‖z - w‖ =
        Real.log ρ + Real.log (ρ⁻¹ * ‖z - w‖) := hlog
    _ ≤ Real.log ρ + Real.posLog (ρ⁻¹ * ‖z - w‖) := by
          have hle : Real.log (ρ⁻¹ * ‖z - w‖) ≤
              Real.posLog (ρ⁻¹ * ‖z - w‖) := by
            rw [Real.posLog_apply]
            exact le_max_right _ _
          linarith
    _ = Real.circleAverage (fun u : ℂ => Real.log ‖u - w‖) z ρ := by
          rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog
            (ne_of_gt hρ)]

/-- The logarithmic kernel has the exact circular mean-value property on
circles whose closed disk does not contain its pole. -/
theorem log_norm_sub_circleAverage_eq_of_radius_le
    (z w : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hsep : ρ ≤ ‖z - w‖) :
    Real.circleAverage (fun u : ℂ => Real.log ‖u - w‖) z ρ =
      Real.log ‖z - w‖ := by
  have hd : 0 < ‖z - w‖ := lt_of_lt_of_le hρ hsep
  have hquot : 0 < ρ⁻¹ * ‖z - w‖ := mul_pos (inv_pos.mpr hρ) hd
  have hge : 1 ≤ |ρ⁻¹ * ‖z - w‖| := by
    rw [abs_of_pos hquot]
    exact (one_le_inv_mul₀ hρ).mpr hsep
  have hfactor : ρ * (ρ⁻¹ * ‖z - w‖) = ‖z - w‖ := by
    field_simp
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog
    (ne_of_gt hρ), Real.posLog_eq_log hge]
  rw [← Real.log_mul (ne_of_gt hρ) (ne_of_gt hquot), hfactor]
end SpringerLean
