import SpringerLean.Round31OuterCircleIntegrable

open MeasureTheory Set Metric Filter
open scoped Topology

namespace SpringerLean

/-- The normalized circle average is continuous under uniform convergence on
the circle once the approximants and limit are genuinely circle integrable. -/
theorem circleAverage_tendsto_of_tendstoUniformlyOn
    (f : ℕ → ℂ → ℝ) (g : ℂ → ℝ) (c : ℂ) (ρ : ℝ)
    (hf : ∀ n, CircleIntegrable (f n) c ρ)
    (hg : CircleIntegrable g c ρ)
    (hlim : TendstoUniformlyOn f g atTop (sphere c |ρ|)) :
    Tendsto (fun n => Real.circleAverage (f n) c ρ) atTop
      (𝓝 (Real.circleAverage g c ρ)) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hhalf : 0 < η / 2 := by linarith
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hlim) (η / 2) hhalf]
    with n hn
  have hdiff : CircleIntegrable (fun z => f n z - g z) c ρ :=
    (hf n).sub hg
  have hbound : Real.circleAverage (fun z => |f n z - g z|) c ρ ≤ η / 2 := by
    apply Real.circleAverage_mono_on_of_le_circle hdiff.abs
    intro z hz
    have h := hn z hz
    simpa [Real.dist_eq, abs_sub_comm] using h.le
  have hmean :
      |Real.circleAverage (f n) c ρ - Real.circleAverage g c ρ| ≤ η / 2 := by
    rw [← Real.circleAverage_fun_sub (hf n) hg]
    exact le_trans Real.abs_circleAverage_le_circleAverage_abs hbound
  change dist (Real.circleAverage (f n) c ρ)
    (Real.circleAverage g c ρ) < η
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hmean (by linarith)

end SpringerLean