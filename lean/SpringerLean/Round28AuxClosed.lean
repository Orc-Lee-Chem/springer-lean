import SpringerLean.Round28AuxBoundary

open MeasureTheory Set

namespace SpringerLean

/-- The actual auxiliary function is continuous on the closed upper half-plane. -/
theorem regularVerticalAuxiliary_continuousOn_upperHalfPlane
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    ContinuousOn (fun p : ℝ × ℝ => regularVerticalAuxiliary F s ξ p.1 p.2)
      {p : ℝ × ℝ | 0 ≤ p.2} := by
  intro p hp
  change 0 ≤ p.2 at hp
  by_cases hp0 : p.2 = 0
  · cases p with
    | mk x y =>
      dsimp at hp0 hp ⊢
      subst y
      exact (regularVerticalAuxiliary_continuousAt_boundary
        F hc hs0 hs1 ξ hξ x).continuousWithinAt
  · have hppos : 0 < p.2 := lt_of_le_of_ne hp (Ne.symm hp0)
    exact (regularVerticalAuxiliary_continuousAt_positive
      F hc hs0 hs1 ξ hξ p.1 p.2 hppos).continuousWithinAt
end SpringerLean