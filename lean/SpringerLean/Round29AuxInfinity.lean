import SpringerLean.Round29AuxVerticalLimsup

namespace SpringerLean

/-- The actual BLP auxiliary has a uniform nonpositive limsup at infinity
in the closed upper half-plane, expressed by an ℓ¹ radius. -/
theorem regularVerticalAuxiliary_infinity_limsup_le_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    ∀ η : ℝ, 0 < η → ∃ R : ℝ, 0 < R ∧
      ∀ (a h : ℝ), 0 ≤ h → R ≤ |a| + h →
        regularVerticalAuxiliary F s ξ a h ≤ η := by
  intro η hη
  obtain ⟨A, hA, hhorizontal⟩ :=
    regularVerticalAuxiliary_horizontal_limsup_le_zero
      F hc hs0 hs1 ξ hξ η hη
  obtain ⟨H, hH, hvertical⟩ :=
    regularVerticalAuxiliary_vertical_limsup_le_zero_on_strip
      F hc hs0 hs1 ξ hξ A η hη
  let R : ℝ := A + H + 1
  have hR : 0 < R := by dsimp [R]; linarith
  refine ⟨R, hR, ?_⟩
  intro a h hh hfar
  by_cases ha : A ≤ |a|
  · exact hhorizontal a h hh ha
  · have ha' : |a| ≤ A := le_of_lt (lt_of_not_ge ha)
    have hHh : H ≤ h := by dsimp [R] at hfar; linarith
    exact hvertical a h ha' hHh

end SpringerLean
