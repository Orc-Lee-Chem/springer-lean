import SpringerLean.Round28CostHeight

open MeasureTheory

namespace SpringerLean

/-- The minimum cost has a uniform local Lipschitz bound in both directions of height. -/
theorem regularVerticalCosts_inf_height_abs_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (a h h' : ℝ), |a| ≤ A → 0 < h → h ≤ H →
        0 < h' → h' ≤ H →
        |sInf (regularVerticalCosts F s ξ a h) -
          sInf (regularVerticalCosts F s ξ a h')| ≤ 2 * M * |h - h'| := by
  obtain ⟨M, hM, hbound⟩ :=
    regularVerticalCosts_inf_height_bound F hc hs0 hs1 ξ hξ A H hA hH
  refine ⟨M, hM, ?_⟩
  intro a h h' ha hh hhH hh' hh'H
  rcases le_total h h' with hle | hle
  · obtain ⟨_, hub⟩ := hbound a h h' ha hh hle hh'H
    have hlow : 0 ≤ sInf (regularVerticalCosts F s ξ a h') -
        sInf (regularVerticalCosts F s ξ a h) :=
      (hbound a h h' ha hh hle hh'H).1
    rw [abs_sub_comm h h', abs_of_nonneg (sub_nonneg.mpr hle)]
    rw [abs_sub_comm]
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  · obtain ⟨hlow, hub⟩ := hbound a h' h ha hh' hle hhH
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
end SpringerLean