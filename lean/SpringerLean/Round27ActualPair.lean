import SpringerLean.Round27MultiplicityIntegral

open MeasureTheory Set
open scoped Classical

namespace SpringerLean

/-- The actual rotated potential respects any exact two-set multiplicity
split. Every integral is certified integrable by the regularized boundary
potential bound. -/
theorem regularExterior_rotated_potential_pair_integral_eq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h ε : ℝ)
    (E : Set ℝ) (hE : E ∈ verticalFeasible h)
    (A B : Set ℝ) (hA : A ∈ verticalFeasible (h + ε))
    (hB : B ∈ verticalFeasible (h - ε))
    (hcount : ∀ t : ℝ,
      (if t ∈ A then (1 : ℕ) else 0) + (if t ∈ B then 1 else 0) =
      (if t ∈ verticalShiftMinus E ε then 1 else 0) +
      (if t ∈ verticalShiftPlus E ε then 1 else 0)) :
    (∫ t in A, regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I)) +
      (∫ t in B, regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ t in verticalShiftMinus E ε,
        regularExteriorRotatedPotential F s ξ
          ((a : ℂ) + (t : ℂ) * Complex.I)) +
      (∫ t in verticalShiftPlus E ε,
        regularExteriorRotatedPotential F s ξ
          ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hP : verticalShiftMinus E ε ∈ verticalFeasible h := by
    exact ⟨verticalShiftMinus_measurable hE.1 ε,
      verticalShiftMinus_bounded E hE.2.1 ε,
      (verticalShiftMinus_volume E ε).trans hE.2.2⟩
  have hQ : verticalShiftPlus E ε ∈ verticalFeasible h := by
    exact ⟨verticalShiftPlus_measurable hE.1 ε,
      verticalShiftPlus_bounded E hE.2.1 ε,
      (verticalShiftPlus_volume E ε).trans hE.2.2⟩
  exact setIntegral_pair_eq_of_indicator_count
    (fun t : ℝ => regularExteriorRotatedPotential F s ξ
      ((a : ℂ) + (t : ℂ) * Complex.I))
    A B (verticalShiftMinus E ε) (verticalShiftPlus E ε)
    hA.1 hB.1 hP.1 hQ.1
    (regularExterior_vertical_cost_integrableOn F hc hs0 hs1 ξ hξ a (h + ε) A hA)
    (regularExterior_vertical_cost_integrableOn F hc hs0 hs1 ξ hξ a (h - ε) B hB)
    (regularExterior_vertical_cost_integrableOn F hc hs0 hs1 ξ hξ a h _ hP)
    (regularExterior_vertical_cost_integrableOn F hc hs0 hs1 ξ hξ a h _ hQ)
    hcount

/-- An actual minimizing vertical set has one radius for all sufficiently
small shifts; at every such shift its exact two-set redistribution preserves
the sum of actual logarithmic-potential costs. -/
theorem regularVerticalCosts_exists_shiftable_minimizer_integral_eq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h) :
    ∃ E ∈ verticalFeasible h,
      (∫ t in E, regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
        sInf (regularVerticalCosts F s ξ a h) ∧
      ∃ δ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ →
        ∃ A ∈ verticalFeasible (h + ε),
          ∃ B ∈ verticalFeasible (h - ε),
            (∫ t in A, regularExteriorRotatedPotential F s ξ
              ((a : ℂ) + (t : ℂ) * Complex.I)) +
              (∫ t in B, regularExteriorRotatedPotential F s ξ
                ((a : ℂ) + (t : ℂ) * Complex.I)) =
              (∫ t in verticalShiftMinus E ε,
                regularExteriorRotatedPotential F s ξ
                  ((a : ℂ) + (t : ℂ) * Complex.I)) +
              (∫ t in verticalShiftPlus E ε,
                regularExteriorRotatedPotential F s ξ
                  ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨E, hE, hmin, δ, hδ, hsplit⟩ :=
    regularVerticalCosts_exists_shiftable_minimizer F hc hs0 hs1 ξ hξ a h hh
  refine ⟨E, hE, hmin, δ, hδ, ?_⟩
  intro ε hε0 hεδ
  obtain ⟨A, hA, B, hB, hcount⟩ := hsplit ε hε0 hεδ
  exact ⟨A, hA, B, hB,
    regularExterior_rotated_potential_pair_integral_eq
      F hc hs0 hs1 ξ hξ a h ε E hE A B hA hB hcount⟩

end SpringerLean
