import SpringerLean.Round28CostHorizontal

open MeasureTheory Set Metric

namespace SpringerLean

/-- For each fixed positive height, the actual minimized vertical cost is
continuous in the horizontal coordinate, with no optimizer parameter. -/
theorem regularVerticalCosts_inf_continuousAt_horizontal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (a h : ℝ) (hh : 0 < h) :
    ContinuousAt (fun x : ℝ => sInf (regularVerticalCosts F s ξ x h)) a := by
  let A : ℝ := |a| + 1
  let H : ℝ := h + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hH : 0 ≤ H := by dsimp [H]; linarith
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ :=
    regularVerticalCosts_inf_uniform_horizontal
      F hc hs0 hs1 ξ hξ A H hA hH ε hε
  refine ⟨min δ 1, lt_min hδ (by norm_num), ?_⟩
  intro x hx
  have hxa : |x - a| < δ := by
    simpa [Real.dist_eq] using lt_of_lt_of_le hx (min_le_left _ _)
  have hxa1 : |x - a| < 1 := by
    simpa [Real.dist_eq] using lt_of_lt_of_le hx (min_le_right _ _)
  have hxA : |x| ≤ A := by
    have htri : |x| ≤ |x - a| + |a| := by
      calc
        |x| = |(x - a) + a| := by ring
        _ ≤ |x - a| + |a| := abs_add_le _ _
    dsimp [A]
    linarith
  have haA : |a| ≤ A := by dsimp [A]; linarith
  have hhH : h ≤ H := by dsimp [H]; linarith
  have h := hclose x a h hxA haA hh hhH hxa
  simpa only [Real.dist_eq] using h

end SpringerLean