import SpringerLean.Round28CostHeightAbs
import SpringerLean.Round28CostHorizontal

open MeasureTheory

namespace SpringerLean

/-- The actual minimized vertical cost is jointly continuous at every positive height. -/
theorem regularVerticalCosts_inf_continuousAt_positive
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (a h : ℝ) (hh : 0 < h) :
    ContinuousAt
      (fun p : ℝ × ℝ => sInf (regularVerticalCosts F s ξ p.1 p.2)) (a, h) := by
  let A : ℝ := |a| + 1
  let H : ℝ := h + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  obtain ⟨M, hM, hheight⟩ :=
    regularVerticalCosts_inf_height_abs_bound F hc hs0 hs1 ξ hξ A H hA hH
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ₁, hδ₁, hhorizontal⟩ :=
    regularVerticalCosts_inf_uniform_horizontal
      F hc hs0 hs1 ξ hξ A H hA hH (ε / 2) (by positivity)
  let δ : ℝ := min δ₁ (min (ε / (4 * M + 1)) (min 1 (h / 2)))
  have hden : 0 < 4 * M + 1 := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro p hp
  have hp1 : |p.1 - a| < δ := by
    have h := lt_of_le_of_lt (le_max_left (dist p.1 a) (dist p.2 h)) hp
    simpa [Prod.dist_eq, Real.dist_eq] using h
  have hp2 : |p.2 - h| < δ := by
    have h := lt_of_le_of_lt (le_max_right (dist p.1 a) (dist p.2 h)) hp
    simpa [Prod.dist_eq, Real.dist_eq] using h
  have hδ₁' : δ ≤ δ₁ := by dsimp [δ]; exact min_le_left _ _
  have hδ₂' : δ ≤ ε / (4 * M + 1) := by
    dsimp [δ]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hδone : δ ≤ 1 := by
    dsimp [δ]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδh : δ ≤ h / 2 := by
    dsimp [δ]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have ha' : |p.1| ≤ A := by
    have := abs_add_le (p.1 - a) a
    dsimp [A]
    rw [sub_add_cancel] at this
    linarith
  have ha : |a| ≤ A := by dsimp [A]; linarith
  have hp2pos : 0 < p.2 := by
    have := (abs_lt.mp (lt_of_lt_of_le hp2 hδh)).1
    linarith
  have hp2H : p.2 ≤ H := by
    have := (abs_lt.mp (lt_of_lt_of_le hp2 hδone)).2
    dsimp [H]
    linarith
  have hhH : h ≤ H := by dsimp [H]; linarith
  have hhor := hhorizontal p.1 a h ha' ha hh hhH
    (lt_of_lt_of_le hp1 hδ₁')
  have hvert := hheight p.1 p.2 h ha' hp2pos hp2H hh hhH
  have hvertSmall :
      |sInf (regularVerticalCosts F s ξ p.1 p.2) -
        sInf (regularVerticalCosts F s ξ p.1 h)| < ε / 2 := by
    have hbound := (mul_le_mul_of_nonneg_left (le_of_lt (lt_of_lt_of_le hp2 hδ₂'))
      (by positivity : 0 ≤ 2 * M))
    have hcalc : 2 * M * (ε / (4 * M + 1)) < ε / 2 := by
      have hmul : (ε / (4 * M + 1)) * (4 * M + 1) = ε := by
        field_simp
      nlinarith [hmul, div_pos hε hden]
    exact lt_of_le_of_lt (hvert.trans hbound) hcalc
  have htriangle := abs_add_le
    (sInf (regularVerticalCosts F s ξ p.1 p.2) -
      sInf (regularVerticalCosts F s ξ p.1 h))
    (sInf (regularVerticalCosts F s ξ p.1 h) -
      sInf (regularVerticalCosts F s ξ a h))
  have hsum :
      sInf (regularVerticalCosts F s ξ p.1 p.2) -
        sInf (regularVerticalCosts F s ξ a h) =
      (sInf (regularVerticalCosts F s ξ p.1 p.2) -
        sInf (regularVerticalCosts F s ξ p.1 h)) +
      (sInf (regularVerticalCosts F s ξ p.1 h) -
        sInf (regularVerticalCosts F s ξ a h)) := by ring
  rw [Real.dist_eq, hsum]
  linarith
end SpringerLean