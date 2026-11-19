import SpringerLean.Round28ComparisonHorizontalUniform

open MeasureTheory Set

namespace SpringerLean

/-- The actual comparison-potential interval integral is jointly continuous at positive height. -/
theorem comparisonSegmentPotential_interval_integral_continuousAt_positive
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h) :
    ContinuousAt
      (fun p : ℝ × ℝ => ∫ t in Icc (-p.2) p.2,
        comparisonSegmentPotential ((p.1 : ℂ) + (t : ℂ) * Complex.I)) (a, h) := by
  let C : ℝ → ℝ → ℝ := fun x y => ∫ t in Icc (-y) y,
    comparisonSegmentPotential ((x : ℂ) + (t : ℂ) * Complex.I)
  have hheight : ContinuousAt (C a) h :=
    comparisonSegmentPotential_interval_integral_continuousAt_height
      F hc hs0 hs1 ξ hξ a h hh
  let A : ℝ := |a| + 1
  let H : ℝ := h + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ₁, hδ₁, hhor⟩ :=
    comparisonSegmentPotential_interval_integral_uniform_horizontal
      F hc hs0 hs1 ξ hξ A H hA hH (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, hheight'⟩ :=
    Metric.continuousAt_iff.mp hheight (ε / 2) (by positivity)
  let δ : ℝ := min δ₁ (min δ₂ (min 1 (h / 2)))
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
  have hδ₂' : δ ≤ δ₂ := by
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
  have hhor' : |C p.1 p.2 - C a p.2| < ε / 2 :=
    hhor p.1 a p.2 ha' ha hp2pos.le hp2H (lt_of_lt_of_le hp1 hδ₁')
  have hheight'' : |C a p.2 - C a h| < ε / 2 := by
    have := hheight' (by
      simpa [Real.dist_eq] using (lt_of_lt_of_le hp2 hδ₂'))
    simpa [Real.dist_eq] using this
  have htriangle := abs_add_le (C p.1 p.2 - C a p.2) (C a p.2 - C a h)
  have hsum : C p.1 p.2 - C a h =
      (C p.1 p.2 - C a p.2) + (C a p.2 - C a h) := by ring
  change dist (C p.1 p.2) (C a h) < ε
  rw [Real.dist_eq, hsum]
  linarith
end SpringerLean