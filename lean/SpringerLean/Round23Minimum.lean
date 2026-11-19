import SpringerLean.Round23Candidate

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean

/-- A set containing every point below a cost threshold and no point above
it minimizes the cost among sets of equal mass. -/
theorem threshold_candidate_integral_le
    (f : ℝ → ℝ) (ell : ℝ) (E B : Set ℝ)
    (hEmeas : MeasurableSet E) (hBmeas : MeasurableSet B)
    (hEfin : volume E ≠ ∞) (hBfin : volume B ≠ ∞)
    (hmass : volume E = volume B)
    (hbelow : {t : ℝ | f t < ell} ⊆ E)
    (habove : E ⊆ {t : ℝ | f t ≤ ell})
    (hIntE : IntegrableOn f E) (hIntB : IntegrableOn f B) :
    (∫ t in E, f t) ≤ ∫ t in B, f t := by
  let g : ℝ → ℝ := fun t => f t - ell
  have hIntgE : IntegrableOn g E :=
    hIntE.sub (integrableOn_const hEfin)
  have hIntgB : IntegrableOn g B :=
    hIntB.sub (integrableOn_const hBfin)
  have hI : MeasurableSet (E ∩ B) := hEmeas.inter hBmeas
  have hdiffE := setIntegral_sdiff hI hIntgE inter_subset_left
  have hdiffB := setIntegral_sdiff hI hIntgB inter_subset_right
  have hsetE : E \ (E ∩ B) = E \ B := by ext t; simp
  have hsetB : B \ (E ∩ B) = B \ E := by ext t; simp [and_comm]
  rw [hsetE] at hdiffE
  rw [hsetB] at hdiffB
  have hneg : (∫ t in E \ B, g t) ≤ 0 := by
    apply setIntegral_nonpos (hEmeas.diff hBmeas)
    intro t ht
    have htE : t ∈ E := ht.1
    have hle : f t ≤ ell := habove htE
    dsimp [g]
    linarith
  have hpos : 0 ≤ (∫ t in B \ E, g t) := by
    apply setIntegral_nonneg (hBmeas.diff hEmeas)
    intro t ht
    have hle : ell ≤ f t := le_of_not_gt (fun h => ht.2 (hbelow h))
    dsimp [g]
    linarith
  have hgle : (∫ t in E, g t) ≤ ∫ t in B, g t := by
    linarith
  have hlinE : (∫ t in E, g t) =
      (∫ t in E, f t) - ell * volume.real E := by
    dsimp [g]
    rw [integral_sub hIntE (integrableOn_const hEfin), setIntegral_const]
    simp [smul_eq_mul, mul_comm]
  have hlinB : (∫ t in B, g t) =
      (∫ t in B, f t) - ell * volume.real B := by
    dsimp [g]
    rw [integral_sub hIntB (integrableOn_const hBfin), setIntegral_const]
    simp [smul_eq_mul, mul_comm]
  rw [hlinE, hlinB] at hgle
  have hreal : volume.real E = volume.real B := by
    simp only [Measure.real_def, hmass]
  rw [hreal] at hgle
  linarith

/-- The infimum of the actual regularized vertical cost is attained by a
bounded measurable set of the prescribed mass. No optimizer or boundary
regularity is assumed in this statement. -/
theorem regularVerticalCosts_exists_minimizer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h) :
    ∃ E ∈ verticalFeasible h,
      (∫ t in E, regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
        sInf (regularVerticalCosts F s ξ a h) := by
  obtain ⟨ell, E, hE, hbelow, habove⟩ :=
    regularExterior_vertical_threshold_candidate
      F hc hs0 hs1 ξ hξ a h hh
  let f : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ
    ((a : ℂ) + (t : ℂ) * Complex.I)
  have hminimal : ∀ B ∈ verticalFeasible h,
      (∫ t in E, f t) ≤ ∫ t in B, f t := by
    intro B hB
    apply threshold_candidate_integral_le f ell E B
    · exact hE.1
    · exact hB.1
    · rw [hE.2.2]
      finiteness
    · rw [hB.2.2]
      finiteness
    · rw [hE.2.2, hB.2.2]
    · exact hbelow
    · exact habove
    · exact regularExterior_vertical_cost_integrableOn
        F hc hs0 hs1 ξ hξ a h E hE
    · exact regularExterior_vertical_cost_integrableOn
        F hc hs0 hs1 ξ hξ a h B hB
  refine ⟨E, hE, le_antisymm ?_ ?_⟩
  · apply le_csInf (regularVerticalCosts_nonempty F s ξ a h)
    rintro q ⟨B, hB, rfl⟩
    exact hminimal B hB
  · apply csInf_le (regularVerticalCosts_bddBelow F hc hs0 hs1 ξ hξ a h)
    exact ⟨E, hE, rfl⟩

end SpringerLean
