import SpringerLean.Round30ComparisonOuterMean
import SpringerLean.Round27CostComparison
import SpringerLean.Round28ComparisonHeight

open MeasureTheory Set

namespace SpringerLean

/-- The one actual minimizer from the small-shift theorem gives a numerical
lower bound for the pair of auxiliary values at heights h±ε. The center
intervals are rewritten using their exact translation multiplicity. -/
theorem regularVerticalAuxiliary_two_height_lower_of_shiftable_minimizer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h) :
    ∃ E ∈ verticalFeasible h,
      (∫ t in E, regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
          sInf (regularVerticalCosts F s ξ a h) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ → ∀ x : ℝ,
        2 * (∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ x t) +
          (∫ t in Icc (-h) h,
            comparisonSegmentPotential
              ((x : ℂ) + ((t - ε : ℝ) : ℂ) * Complex.I)) +
          (∫ t in Icc (-h) h,
            comparisonSegmentPotential
              ((x : ℂ) + ((t + ε : ℝ) : ℂ) * Complex.I)) -
          ((∫ t in E, regularExteriorRotatedPotential F s ξ
              ((x : ℂ) + ((t - ε : ℝ) : ℂ) * Complex.I)) +
           (∫ t in E, regularExteriorRotatedPotential F s ξ
              ((x : ℂ) + ((t + ε : ℝ) : ℂ) * Complex.I))) ≤
        regularVerticalAuxiliary F s ξ x (h + ε) +
          regularVerticalAuxiliary F s ξ x (h - ε) := by
  obtain ⟨E, hE, hmin, δ₀, hδ₀, hsplit⟩ :=
    regularVerticalCosts_two_height_le_shifted_actual_cost
      F hc hs0 hs1 ξ hξ a h hh
  let δ : ℝ := min δ₀ h
  have hδ : 0 < δ := lt_min hδ₀ hh
  refine ⟨E, hE, hmin, δ, hδ, ?_⟩
  intro ε hε0 hεδ x
  have hεδ₀ : ε < δ₀ := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεh : ε < h := lt_of_lt_of_le hεδ (min_le_right _ _)
  have hhplus : 0 < h + ε := by linarith
  have hhminus : 0 < h - ε := by linarith
  have hcost := hsplit ε hε0 hεδ₀ x
  let G : ℝ → ℝ := fun t => comparisonSegmentPotential
    ((x : ℂ) + (t : ℂ) * Complex.I)
  have hGint (u v : ℝ) : IntegrableOn G (Icc u v) := by
    by_cases huv : u ≤ v
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le huv).mp
        (comparisonSegmentPotential_vertical_intervalIntegrable
          F hc hs0 hs1 ξ hξ x u v)
    · have hset : Icc u v = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge huv)
      rw [hset]
      simp
  have hcomp := centered_interval_shift_integral_pair
    G h ε hε0 hεh.le hGint
  rw [setIntegral_verticalShiftMinus G (Icc (-h) h) measurableSet_Icc ε,
    setIntegral_verticalShiftPlus G (Icc (-h) h) measurableSet_Icc ε] at hcomp
  have hUplus : regularVerticalAuxiliary F s ξ x (h + ε) =
      (∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ x t) +
      (∫ t in Icc (-(h + ε)) (h + ε), G t) -
      sInf (regularVerticalCosts F s ξ x (h + ε)) := by
    simp [regularVerticalAuxiliary, not_le.mpr hhplus, G]
  have hUminus : regularVerticalAuxiliary F s ξ x (h - ε) =
      (∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ x t) +
      (∫ t in Icc (-(h - ε)) (h - ε), G t) -
      sInf (regularVerticalCosts F s ξ x (h - ε)) := by
    simp [regularVerticalAuxiliary, not_le.mpr hhminus, G]
  rw [hUplus, hUminus]
  dsimp [G] at hcomp hcost
  linarith

end SpringerLean
