import SpringerLean.Round27VerticalCircleSwapMeasurable

open MeasureTheory Set Metric

namespace SpringerLean

/-- The actual rotated logarithmic potential admits Fubini over every
bounded measurable vertical set and every circle. The proof uses its
measurability and a uniform linear bound, so it remains valid at boundary
contact points where the individual logarithmic kernel is singular. -/
theorem regularExterior_rotated_potential_vertical_circle_swap
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (c : ℂ) (ρ : ℝ) :
    (∫ t in E, Real.circleAverage
      (fun z : ℂ => regularExteriorRotatedPotential F s ξ
        (z + (t : ℂ) * Complex.I)) c ρ) =
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
  have hbound : ∀ t ∈ E, ∀ z ∈ sphere c |ρ|,
      ‖f t z‖ ≤ ‖c‖ + |ρ| + B + C + 1 := by
    intro t ht z hz
    have htB : |t| ≤ B := by simpa [Real.norm_eq_abs] using hB t ht
    have hzB : ‖z‖ ≤ ‖c‖ + |ρ| := by
      have hdist : ‖z - c‖ = |ρ| := by
        simpa only [mem_sphere, dist_eq_norm] using hz
      have htri : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
        calc
          ‖z‖ = ‖(z - c) + c‖ := by congr 1; abel
          _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      linarith
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
  exact setIntegral_circleAverage_swap_of_measurable_bounded
    f hf E hEm hEb c ρ _ hbound

end SpringerLean