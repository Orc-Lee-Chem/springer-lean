import SpringerLean.Round27IntegratedSubmean
set_option maxHeartbeats 1000000

open MeasureTheory Set Metric

namespace SpringerLean

private theorem circleAverage_vertical_translate
    (P : ℂ → ℝ) (c : ℂ) (t ρ : ℝ) :
    Real.circleAverage (fun z : ℂ => P (z + (t : ℂ) * Complex.I)) c ρ =
      Real.circleAverage P (c + (t : ℂ) * Complex.I) ρ := by
  rw [Real.circleAverage_def, Real.circleAverage_def]
  congr 1
  simp only [circleMap]
  apply intervalIntegral.integral_congr
  intro θ hθ
  congr 1
  ring

/-- The actual rotated logarithmic potential's global submean inequality
remains valid after integrating over any bounded measurable vertical set.
This is the input for the auxiliary-function circle comparison. -/
theorem regularExterior_rotated_potential_vertical_integral_submean
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ t in E, regularExteriorRotatedPotential F s ξ
      (c + (t : ℂ) * Complex.I)) ≤
      Real.circleAverage
        (fun z : ℂ => ∫ t in E,
          regularExteriorRotatedPotential F s ξ
            (z + (t : ℂ) * Complex.I)) c ρ := by
  let P := regularExteriorRotatedPotential F s ξ
  let f : ℝ → ℂ → ℝ := fun t z => P (z + (t : ℂ) * Complex.I)
  have hf : Measurable (fun p : ℝ × ℂ => f p.1 p.2) := by
    have hP := regularExterior_rotated_potential_measurable F hc hs0 hs1 ξ hξ
    exact hP.comp (by fun_prop)
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp hEb
  obtain ⟨C, hC0, hC⟩ :=
    regularExterior_boundary_potential_linear_bound F hc hs0 hs1
  have hpoint_bound (t : ℝ) (ht : t ∈ E) (z : ℂ) :
      ‖f t z‖ ≤ ‖z‖ + B + C + 1 := by
    have htB : |t| ≤ B := by simpa [Real.norm_eq_abs] using hB t ht
    have hPnonneg : 0 ≤ f t z :=
      regularExterior_rotated_boundary_potential_nonneg
        F hc hs0 hs1 ξ hξ _
    have hPbound := hC (ξ * (z + (t : ℂ) * Complex.I))
    rw [← regularExterior_rotated_potential_eq F s ξ hξ,
      norm_mul, hξ, one_mul] at hPbound
    have hline : ‖z + (t : ℂ) * Complex.I‖ ≤ ‖z‖ + |t| := by
      calc
        ‖z + (t : ℂ) * Complex.I‖ ≤ ‖z‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = ‖z‖ + |t| := by simp
    change ‖P (z + (t : ℂ) * Complex.I)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg hPnonneg]
    linarith
  have hbound : ∀ t ∈ E, ∀ z ∈ sphere c |ρ|,
      ‖f t z‖ ≤ ‖c‖ + |ρ| + B + C + 1 := by
    intro t ht z hz
    have hdist : ‖z - c‖ = |ρ| := by
      simpa only [mem_sphere, dist_eq_norm] using hz
    have hzB : ‖z‖ ≤ ‖c‖ + |ρ| := by
      have htri : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
        calc
          ‖z‖ = ‖(z - c) + c‖ := by congr 1; abel
          _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      linarith
    exact le_trans (hpoint_bound t ht z) (by linarith)
  have hcenter : IntegrableOn (fun t => f t c) E := by
    have hmeas : Measurable (fun t : ℝ => f t c) := by
      have hp : Measurable (fun t : ℝ => (t, c)) := by fun_prop
      exact hf.comp hp
    apply IntegrableOn.of_bound hEb.measure_lt_top
      hmeas.aestronglyMeasurable (‖c‖ + B + C + 1)
    apply (ae_restrict_iff' hEm).2
    filter_upwards [] with t ht
    exact hpoint_bound t ht c
  have hsub : ∀ t ∈ E, f t c ≤ Real.circleAverage (f t) c ρ := by
    intro t ht
    change P (c + (t : ℂ) * Complex.I) ≤
      Real.circleAverage (fun z : ℂ => P (z + (t : ℂ) * Complex.I)) c ρ
    rw [circleAverage_vertical_translate]
    exact regularExterior_rotated_potential_circle_submean
      F hc hs0 hs1 ξ hξ _ ρ hρ
  exact setIntegral_le_circleAverage_setIntegral_of_pointwise_submean
    f hf E hEm hEb c ρ _ hbound hcenter hsub

end SpringerLean