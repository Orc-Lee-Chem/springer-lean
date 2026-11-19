import SpringerLean.Round28CostHorizontalAt

open MeasureTheory Set Metric
open scoped ENNReal

namespace SpringerLean

/-- The actual regularized potential integrated on a fixed centered
vertical interval varies continuously with the horizontal coordinate. -/
theorem regularExterior_rotated_potential_interval_integral_continuousAt_horizontal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (a h : ℝ) (hh : 0 < h) :
    ContinuousAt
      (fun x : ℝ => ∫ t in Icc (-h) h,
        regularExteriorRotatedPotential F s ξ ((x : ℂ) + (t : ℂ) * Complex.I)) a := by
  let A : ℝ := |a| + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : Icc (-h) h ∈ verticalFeasible h := by
    simpa using centered_interval_verticalFeasible h 0
  have hmass : volume.real (Icc (-h) h) = 2 * h := by
    rw [Measure.real_def, hE.2.2, ENNReal.toReal_ofReal (by linarith)]
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let η : ℝ := ε / (2 * h + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ, hδ, hstrip⟩ :=
    regularExterior_rotated_potential_uniform_horizontal_on_strip
      F hc hs0 hs1 ξ hξ A h hA hh.le η hη
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
  have hIntx := regularExterior_vertical_cost_integrableOn
    F hc hs0 hs1 ξ hξ x h (Icc (-h) h) hE
  have hInta := regularExterior_vertical_cost_integrableOn
    F hc hs0 hs1 ξ hξ a h (Icc (-h) h) hE
  have hEfin : volume (Icc (-h) h) ≠ ∞ := by
    rw [hE.2.2]
    finiteness
  have hpoint : ∀ t ∈ Icc (-h) h,
      |regularExteriorRotatedPotential F s ξ ((x : ℂ) + (t : ℂ) * Complex.I) -
        regularExteriorRotatedPotential F s ξ ((a : ℂ) + (t : ℂ) * Complex.I)| ≤ η := by
    intro t ht
    have htBound : |t| ≤ h := abs_le.mpr ht
    exact le_of_lt (hstrip x a t hxA haA htBound hxa)
  have hbound := abs_setIntegral_sub_le_of_uniform_bound
    (Icc (-h) h) measurableSet_Icc hEfin
    (fun t => regularExteriorRotatedPotential F s ξ ((x : ℂ) + (t : ℂ) * Complex.I))
    (fun t => regularExteriorRotatedPotential F s ξ ((a : ℂ) + (t : ℂ) * Complex.I))
    hIntx hInta η hη.le hpoint
  rw [hmass] at hbound
  change dist
    (∫ t in Icc (-h) h,
      regularExteriorRotatedPotential F s ξ ((x : ℂ) + (t : ℂ) * Complex.I))
    (∫ t in Icc (-h) h,
      regularExteriorRotatedPotential F s ξ ((a : ℂ) + (t : ℂ) * Complex.I)) < ε
  rw [Real.dist_eq]
  have hratio : η * (2 * h + 1) = ε := by
    dsimp [η]
    field_simp
  nlinarith

end SpringerLean