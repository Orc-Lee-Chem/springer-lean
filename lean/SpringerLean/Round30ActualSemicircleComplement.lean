import SpringerLean.Round30ActualPairComplement

open MeasureTheory Set

namespace SpringerLean

/-- At every angle on every sufficiently small semicircle, the actual
auxiliary pair dominates the two finite-window complements formed from one
and the same genuine minimizing set. -/
theorem regularVerticalAuxiliary_semicircle_finite_complement_lower
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h) :
    ∃ E ∈ verticalFeasible h, ∃ T : ℝ,
      h ≤ T ∧ E ⊆ Icc (-T) T ∧
      (∫ t in E, regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
          sInf (regularVerticalCosts F s ξ a h) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 ≤ ρ → ρ < δ →
        ∀ θ ∈ Icc (0 : ℝ) Real.pi,
          regularVerticalFiniteComplement F s ξ
              (a + ρ * Real.cos θ) h T (- (ρ * Real.sin θ)) E +
            regularVerticalFiniteComplement F s ξ
              (a + ρ * Real.cos θ) h T (ρ * Real.sin θ) E ≤
            regularVerticalAuxiliary F s ξ
              (a + ρ * Real.cos θ) (h + ρ * Real.sin θ) +
            regularVerticalAuxiliary F s ξ
              (a + ρ * Real.cos θ) (h - ρ * Real.sin θ) := by
  obtain ⟨E, hE, hmin, δ, hδ, hpair⟩ :=
    regularVerticalAuxiliary_actual_semicircle_pair_lower
      F hc hs0 hs1 ξ hξ a h hh
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp hE.2.1
  let T : ℝ := max h B
  have hT : h ≤ T := le_max_left _ _
  have hBT : B ≤ T := le_max_right _ _
  have hES : E ⊆ Icc (-T) T := by
    intro t ht
    have htB : |t| ≤ B := by simpa [Real.norm_eq_abs] using hB t ht
    have htBounds := abs_le.mp htB
    exact ⟨by linarith [htBounds.1], by linarith [htBounds.2]⟩
  refine ⟨E, hE, T, hT, hES, hmin, δ, hδ, ?_⟩
  intro ρ hρ hρδ θ hθ
  have heq := regularExterior_actual_finite_complements_pair
    F hc hs0 hs1 ξ hξ (a + ρ * Real.cos θ) h T
      (ρ * Real.sin θ) hh hT E hE.1 hES
  rw [← heq]
  exact hpair ρ hρ hρδ θ hθ

end SpringerLean