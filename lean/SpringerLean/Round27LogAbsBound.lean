import SpringerLean.Round27ActualCircleSwap

open MeasureTheory Set Metric
open scoped Real

namespace SpringerLean

/-- Uniform control of the logarithmic singularity on a circle. The bound is
valid even when the pole lies on the integration circle. -/
theorem log_norm_circleAverage_abs_le
    (c w : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    Real.circleAverage (fun u : ℂ => |Real.log ‖u - w‖|) c ρ ≤
      2 * (‖c‖ + |ρ| + ‖w‖ + 1) - Real.log ρ := by
  let D : ℝ := ‖c‖ + |ρ| + ‖w‖ + 1
  have hlogint : CircleIntegrable (fun u : ℂ => Real.log ‖u - w‖) c ρ :=
    circleIntegrable_log_norm_sub_const ρ
  have habs : CircleIntegrable (fun u : ℂ => |Real.log ‖u - w‖|) c ρ :=
    hlogint.abs
  have hconst : CircleIntegrable (fun _ : ℂ => (2 * D : ℝ)) c ρ :=
    circleIntegrable_const _ _ _
  have hright : CircleIntegrable
      (fun u : ℂ => 2 * D - Real.log ‖u - w‖) c ρ := hconst.sub hlogint
  have hpoint : ∀ u ∈ sphere c |ρ|,
      |Real.log ‖u - w‖| ≤ 2 * D - Real.log ‖u - w‖ := by
    intro u hu
    have hdist : ‖u - c‖ = |ρ| := by
      simpa only [mem_sphere, dist_eq_norm] using hu
    have hu : ‖u‖ ≤ ‖c‖ + |ρ| := by
      have htri : ‖u‖ ≤ ‖u - c‖ + ‖c‖ := by
        calc
          ‖u‖ = ‖(u - c) + c‖ := by congr 1; abel
          _ ≤ ‖u - c‖ + ‖c‖ := norm_add_le _ _
      linarith
    have hnorm : ‖u - w‖ ≤ ‖u‖ + ‖w‖ := norm_sub_le _ _
    have hlog := Real.log_le_self (norm_nonneg (u - w))
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hupper : Real.log ‖u - w‖ ≤ D := by dsimp [D]; linarith
    rcases le_total (Real.log ‖u - w‖) 0 with h | h
    · rw [abs_of_nonpos h]; linarith
    · rw [abs_of_nonneg h]; linarith
  have hm := Real.circleAverage_mono habs hright hpoint
  change Real.circleAverage (fun u : ℂ => |Real.log ‖u - w‖|) c ρ ≤
    Real.circleAverage ((fun _ : ℂ => 2 * D) - fun u => Real.log ‖u - w‖) c ρ at hm
  rw [Real.circleAverage_sub hconst hlogint, Real.circleAverage_const] at hm
  have hform := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog
    (c := c) (a := w) (R := ρ) (ne_of_gt hρ)
  rw [hform] at hm
  have hpos : 0 ≤ Real.posLog (ρ⁻¹ * ‖c - w‖) := by
    rw [Real.posLog_apply]
    exact le_max_left _ _
  dsimp [D] at hm ⊢
  linarith

end SpringerLean