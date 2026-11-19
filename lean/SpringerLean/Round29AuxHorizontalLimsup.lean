import SpringerLean.Round29AuxClosedHorizontal

namespace SpringerLean

/-- Along either horizontal end of the closed upper half-plane, the actual
auxiliary has limsup at most zero uniformly over all heights. -/
theorem regularVerticalAuxiliary_horizontal_limsup_le_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    ∀ η : ℝ, 0 < η → ∃ R : ℝ, 0 < R ∧
      ∀ (a h : ℝ), 0 ≤ h → R ≤ |a| →
        regularVerticalAuxiliary F s ξ a h ≤ η := by
  obtain ⟨C, hC0, hbound⟩ :=
    regularVerticalAuxiliary_horizontal_decay_bound_nonneg
      F hc hs0 hs1 ξ hξ
  intro η hη
  let R : ℝ := 1 + C * Real.pi / η
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, ?_⟩
  intro a h hh ha
  have hsqrt : |a| ≤ Real.sqrt (1 + a ^ 2) := by
    apply (Real.le_sqrt (abs_nonneg a) (by positivity)).2
    rw [sq_abs]
    linarith
  have hsqrtpos : 0 < Real.sqrt (1 + a ^ 2) :=
    Real.sqrt_pos.2 (by positivity)
  have hbound' := hbound a h hh
  apply hbound'.trans
  apply (div_le_iff₀ hsqrtpos).2
  have hRident : η * R = η + C * Real.pi := by
    dsimp [R]
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left (le_trans ha hsqrt) hη.le]

end SpringerLean
