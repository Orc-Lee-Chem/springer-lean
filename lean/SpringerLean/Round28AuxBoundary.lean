import SpringerLean.Round28CostZeroBound
import SpringerLean.Round28ComparisonZero
import SpringerLean.Round28ComparisonHorizontalUniform
import SpringerLean.Round18Continuity

open MeasureTheory Set

namespace SpringerLean

/-- The actual BLP auxiliary function is jointly continuous at every boundary point. -/
theorem regularVerticalAuxiliary_continuousAt_boundary
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => regularVerticalAuxiliary F s ξ p.1 p.2) (a, 0) := by
  let w : ℝ → ℝ := fun x =>
    ∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ x t
  let C : ℝ → ℝ → ℝ := fun x y => ∫ t in Icc (-y) y,
    comparisonSegmentPotential ((x : ℂ) + (t : ℂ) * Complex.I)
  have hw : Continuous w :=
    regularExteriorVerticalPotentialDifference_integral_continuous F hc hs0 hs1 ξ
  have hCzero : C a 0 = 0 := by simp [C]
  have hCcont : ContinuousAt (C a) 0 :=
    comparisonSegmentPotential_interval_integral_continuousAt_zero
      F hc hs0 hs1 ξ hξ a
  let A : ℝ := |a| + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨M, hM, hcost⟩ :=
    regularVerticalCosts_inf_small_height_bound
      F hc hs0 hs1 ξ hξ A 1 hA (by norm_num)
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δw, hδw, hwδ⟩ := Metric.continuousAt_iff.mp hw.continuousAt
    (ε / 4) (by positivity)
  obtain ⟨δc, hδc, hcδ⟩ := Metric.continuousAt_iff.mp hCcont
    (ε / 4) (by positivity)
  obtain ⟨δhor, hδhor, hhor⟩ :=
    comparisonSegmentPotential_interval_integral_uniform_horizontal
      F hc hs0 hs1 ξ hξ A 1 hA (by norm_num) (ε / 4) (by positivity)
  let δ : ℝ := min δw (min δc (min δhor (min 1 (ε / (8 * M + 1)))))
  have hden : 0 < 8 * M + 1 := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro p hp
  have hp1 : |p.1 - a| < δ := by
    have h := lt_of_le_of_lt (le_max_left (dist p.1 a) (dist p.2 0)) hp
    simpa [Prod.dist_eq, Real.dist_eq] using h
  have hp2 : |p.2| < δ := by
    have h := lt_of_le_of_lt (le_max_right (dist p.1 a) (dist p.2 0)) hp
    simpa [Prod.dist_eq, Real.dist_eq] using h
  have hδw : δ ≤ δw := by dsimp [δ]; exact min_le_left _ _
  have hδc : δ ≤ δc := by
    dsimp [δ]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδhor : δ ≤ δhor := by
    dsimp [δ]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδone : δ ≤ 1 := by
    dsimp [δ]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hδcost : δ ≤ ε / (8 * M + 1) := by
    dsimp [δ]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have ha' : |p.1| ≤ A := by
    have := abs_add_le (p.1 - a) a
    dsimp [A]
    rw [sub_add_cancel] at this
    linarith
  have ha : |a| ≤ A := by dsimp [A]; linarith
  have hwdiff : |w p.1 - w a| < ε / 4 := by
    have := hwδ (show dist p.1 a < δw from by
      simpa [Real.dist_eq] using lt_of_lt_of_le hp1 hδw)
    simpa [Real.dist_eq] using this
  have hbase : regularVerticalAuxiliary F s ξ a 0 = w a :=
    regularVerticalAuxiliary_boundary F s ξ a
  by_cases hp2le : p.2 ≤ 0
  · have hval : regularVerticalAuxiliary F s ξ p.1 p.2 = w p.1 := by
      simp [regularVerticalAuxiliary, hp2le, w]
    rw [Real.dist_eq, hval, hbase]
    linarith
  · have hp2pos : 0 < p.2 := lt_of_not_ge hp2le
    have hp2one : p.2 ≤ 1 := by
      have := (abs_lt.mp (lt_of_lt_of_le hp2 hδone)).2
      linarith
    have hhor' : |C p.1 p.2 - C a p.2| < ε / 4 :=
      hhor p.1 a p.2 ha' ha hp2pos.le hp2one (lt_of_lt_of_le hp1 hδhor)
    have hcomp' : |C a p.2| < ε / 4 := by
      have h := hcδ (show dist p.2 0 < δc from by
        simpa [Real.dist_eq] using lt_of_lt_of_le hp2 hδc)
      simpa [Real.dist_eq, hCzero] using h
    have hcost' := hcost p.1 p.2 ha' hp2pos.le hp2one
    have hcostsmall : 2 * M * p.2 < ε / 4 := by
      have hmul : (ε / (8 * M + 1)) * (8 * M + 1) = ε := by field_simp
      have hp2bound : p.2 < ε / (8 * M + 1) := by
        have := lt_of_lt_of_le hp2 hδcost
        rw [abs_of_pos hp2pos] at this
        exact this
      nlinarith [hmul]
    have hcompAbs : |C p.1 p.2| < ε / 2 := by
      have htri := abs_add_le (C p.1 p.2 - C a p.2) (C a p.2)
      have hsum : C p.1 p.2 = (C p.1 p.2 - C a p.2) + C a p.2 := by ring
      rw [hsum]
      linarith
    have hval : regularVerticalAuxiliary F s ξ p.1 p.2 =
        w p.1 + C p.1 p.2 - sInf (regularVerticalCosts F s ξ p.1 p.2) := by
      simp [regularVerticalAuxiliary, not_le.mpr hp2pos, w, C]
    rw [Real.dist_eq, hval, hbase]
    have htri := abs_add_le (w p.1 - w a)
      (C p.1 p.2 - sInf (regularVerticalCosts F s ξ p.1 p.2))
    have htri2 : |C p.1 p.2 - sInf (regularVerticalCosts F s ξ p.1 p.2)| ≤
        |C p.1 p.2| + |sInf (regularVerticalCosts F s ξ p.1 p.2)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (C p.1 p.2) (-sInf (regularVerticalCosts F s ξ p.1 p.2))
    have hcostAbs : |sInf (regularVerticalCosts F s ξ p.1 p.2)| ≤
        2 * M * p.2 := by
      rw [abs_of_nonneg hcost'.1]
      exact hcost'.2
    have hsum : w p.1 + C p.1 p.2 -
        sInf (regularVerticalCosts F s ξ p.1 p.2) - w a =
        (w p.1 - w a) +
        (C p.1 p.2 - sInf (regularVerticalCosts F s ξ p.1 p.2)) := by ring
    rw [hsum]
    linarith
end SpringerLean