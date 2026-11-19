import SpringerLean.Round30AuxAnglePair
import SpringerLean.Round30AuxPair

open MeasureTheory Set

namespace SpringerLean

/-- One actual minimizing set works for every angle on every sufficiently small
upper semicircle. This is the pointwise input for the angular submean proof. -/
theorem regularVerticalAuxiliary_actual_semicircle_pair_lower
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h) :
    ∃ E ∈ verticalFeasible h,
      (∫ t in E, regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
          sInf (regularVerticalCosts F s ξ a h) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 ≤ ρ → ρ < δ →
        ∀ θ ∈ Icc (0 : ℝ) Real.pi,
        2 * (∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ
          (a + ρ * Real.cos θ) t) +
          (∫ t in Icc (-h) h,
            comparisonSegmentPotential
              (((a + ρ * Real.cos θ : ℝ) : ℂ) +
                ((t - ρ * Real.sin θ : ℝ) : ℂ) * Complex.I)) +
          (∫ t in Icc (-h) h,
            comparisonSegmentPotential
              (((a + ρ * Real.cos θ : ℝ) : ℂ) +
                ((t + ρ * Real.sin θ : ℝ) : ℂ) * Complex.I)) -
          ((∫ t in E, regularExteriorRotatedPotential F s ξ
              (((a + ρ * Real.cos θ : ℝ) : ℂ) +
                ((t - ρ * Real.sin θ : ℝ) : ℂ) * Complex.I)) +
           (∫ t in E, regularExteriorRotatedPotential F s ξ
              (((a + ρ * Real.cos θ : ℝ) : ℂ) +
                ((t + ρ * Real.sin θ : ℝ) : ℂ) * Complex.I))) ≤
          regularVerticalAuxiliary F s ξ
            (a + ρ * Real.cos θ) (h + ρ * Real.sin θ) +
          regularVerticalAuxiliary F s ξ
            (a + ρ * Real.cos θ) (h - ρ * Real.sin θ) := by
  obtain ⟨E, hE, hmin, δ, hδ, hpair⟩ :=
    regularVerticalAuxiliary_two_height_lower_of_shiftable_minimizer
      F hc hs0 hs1 ξ hξ a h hh
  refine ⟨E, hE, hmin, δ, hδ, ?_⟩
  intro ρ hρ hρδ θ hθ
  have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc hθ
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hε0 : 0 ≤ ρ * Real.sin θ := mul_nonneg hρ hsin0
  have hεδ : ρ * Real.sin θ < δ := by
    have hmul : ρ * Real.sin θ ≤ ρ := by nlinarith
    exact lt_of_le_of_lt hmul hρδ
  exact hpair (ρ * Real.sin θ) hε0 hεδ (a + ρ * Real.cos θ)

end SpringerLean