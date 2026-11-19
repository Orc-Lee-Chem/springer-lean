import SpringerLean.Round31OuterCircleUniform

open MeasureTheory Set Metric Filter
open scoped Topology

namespace SpringerLean

/-- On a circle, a uniformly convergent sequence of circle-integrable real
functions has a genuinely circle-integrable limit. -/
theorem circleIntegrable_of_tendstoUniformlyOn
    (f : ℕ → ℂ → ℝ) (g : ℂ → ℝ) (c : ℂ) (ρ : ℝ)
    (hf : ∀ n, CircleIntegrable (f n) c ρ)
    (hlim : TendstoUniformlyOn f g atTop (sphere c |ρ|)) :
    CircleIntegrable g c ρ := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hfi (n : ℕ) : Integrable
      (fun θ : ℝ => f n (circleMap c ρ θ)) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mp (hf n)
  have hpoint (θ : ℝ) :
      Tendsto (fun n => f n (circleMap c ρ θ)) atTop
        (𝓝 (g (circleMap c ρ θ))) :=
    hlim.tendsto_at (circleMap_mem_sphere' c ρ θ)
  have hgmeas : AEStronglyMeasurable
      (fun θ : ℝ => g (circleMap c ρ θ)) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hfi n).aestronglyMeasurable)
      (Filter.Eventually.of_forall hpoint)
  obtain ⟨n₀, hn₀⟩ :=
    (Metric.tendstoUniformlyOn_iff.mp hlim) 1 (by norm_num) |>.exists
  have hbound (θ : ℝ) :
      ‖g (circleMap c ρ θ)‖ ≤
        ‖f n₀ (circleMap c ρ θ)‖ + 1 := by
    have hdist := hn₀ (circleMap c ρ θ) (circleMap_mem_sphere' c ρ θ)
    have htri : ‖g (circleMap c ρ θ)‖ ≤
        ‖g (circleMap c ρ θ) - f n₀ (circleMap c ρ θ)‖ +
          ‖f n₀ (circleMap c ρ θ)‖ := by
      calc
        ‖g (circleMap c ρ θ)‖ =
            ‖(g (circleMap c ρ θ) - f n₀ (circleMap c ρ θ)) +
              f n₀ (circleMap c ρ θ)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    have hnorm : ‖g (circleMap c ρ θ) - f n₀ (circleMap c ρ θ)‖ < 1 := by
      simpa [dist_eq_norm, norm_sub_rev] using hdist
    linarith
  have hgin : Integrable (fun θ : ℝ => g (circleMap c ρ θ)) μ := by
    apply Integrable.mono ((hfi n₀).norm.add (integrable_const 1)) hgmeas
    filter_upwards [] with θ
    simp only [Pi.add_apply, Real.norm_eq_abs]
    have hpos : 0 ≤ |f n₀ (circleMap c ρ θ)| + 1 := by positivity
    rw [abs_of_nonneg hpos]
    simpa only [Real.norm_eq_abs] using hbound θ
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).2 hgin

end SpringerLean