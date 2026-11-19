import SpringerLean.Round27CenteredIntervals

open MeasureTheory Set
open scoped Classical

namespace SpringerLean

/-- A single actual minimizing set at the base point controls both nearby
height costs, uniformly over every sufficiently small translation. The
horizontal coordinate `x` is arbitrary and need not equal the base point. -/
theorem regularVerticalCosts_two_height_le_shifted_actual_cost
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h) :
    ∃ E ∈ verticalFeasible h,
      (∫ t in E, regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
        sInf (regularVerticalCosts F s ξ a h) ∧
      ∃ δ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ → ∀ x : ℝ,
        sInf (regularVerticalCosts F s ξ x (h + ε)) +
          sInf (regularVerticalCosts F s ξ x (h - ε)) ≤
        (∫ t in E, regularExteriorRotatedPotential F s ξ
          ((x : ℂ) + ((t - ε : ℝ) : ℂ) * Complex.I)) +
        (∫ t in E, regularExteriorRotatedPotential F s ξ
          ((x : ℂ) + ((t + ε : ℝ) : ℂ) * Complex.I)) := by
  obtain ⟨E, hE, hmin, δ, hδ, hsplit⟩ :=
    regularVerticalCosts_exists_shiftable_minimizer F hc hs0 hs1 ξ hξ a h hh
  refine ⟨E, hE, hmin, δ, hδ, ?_⟩
  intro ε hε0 hεδ x
  obtain ⟨A, hA, B, hB, hcount⟩ := hsplit ε hε0 hεδ
  let f : ℝ → ℝ := fun t =>
    regularExteriorRotatedPotential F s ξ ((x : ℂ) + (t : ℂ) * Complex.I)
  have hleA : sInf (regularVerticalCosts F s ξ x (h + ε)) ≤ ∫ t in A, f t := by
    apply csInf_le (regularVerticalCosts_bddBelow F hc hs0 hs1 ξ hξ x (h + ε))
    exact ⟨A, hA, rfl⟩
  have hleB : sInf (regularVerticalCosts F s ξ x (h - ε)) ≤ ∫ t in B, f t := by
    apply csInf_le (regularVerticalCosts_bddBelow F hc hs0 hs1 ξ hξ x (h - ε))
    exact ⟨B, hB, rfl⟩
  calc
    sInf (regularVerticalCosts F s ξ x (h + ε)) +
        sInf (regularVerticalCosts F s ξ x (h - ε)) ≤
        (∫ t in A, f t) + (∫ t in B, f t) := add_le_add hleA hleB
    _ = (∫ t in verticalShiftMinus E ε, f t) +
        (∫ t in verticalShiftPlus E ε, f t) :=
          regularExterior_rotated_potential_pair_integral_eq
            F hc hs0 hs1 ξ hξ x h ε E hE A B hA hB hcount
    _ = (∫ t in E, f (t - ε)) + (∫ t in E, f (t + ε)) := by
          rw [setIntegral_verticalShiftMinus f E hE.1 ε,
            setIntegral_verticalShiftPlus f E hE.1 ε]
    _ = _ := rfl

end SpringerLean
