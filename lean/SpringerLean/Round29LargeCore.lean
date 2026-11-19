import SpringerLean.Round29AuxHorizontalLimsup
import SpringerLean.Round23Candidate
import SpringerLean.Round28UniformCoercive

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean

/-- At large height, actual threshold minimizers on a bounded horizontal
strip contain every preassigned compact vertical core. -/
theorem regularVerticalCosts_large_height_core_minimizer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (A L : ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ (a h : ℝ), |a| ≤ A → H ≤ h →
      ∃ E ∈ verticalFeasible h,
        Icc (-L) L ⊆ E ∧
        (∫ t in E, regularExteriorRotatedPotential F s ξ
          ((a : ℂ) + (t : ℂ) * Complex.I)) =
          sInf (regularVerticalCosts F s ξ a h) := by
  obtain ⟨C, hC0, hC⟩ :=
    regularExterior_boundary_potential_linear_bound F hc hs0 hs1
  let B : ℝ := A + L + C + 1
  obtain ⟨T, hT0, hT⟩ :=
    regularExterior_rotated_potential_vertical_uniform_coercive
      F hc hs0 hs1 ξ hξ B
  let H : ℝ := T + 1
  have hH : 0 < H := by dsimp [H]; linarith
  refine ⟨H, hH, ?_⟩
  intro a h ha hh
  have hh0 : 0 < h := lt_of_lt_of_le hH hh
  let f : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ
    ((a : ℂ) + (t : ℂ) * Complex.I)
  have hcorebound (t : ℝ) (ht : t ∈ Icc (-L) L) : f t ≤ B := by
    have htL : |t| ≤ L := abs_le.mpr ht
    let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
    have hzbound : ‖z‖ ≤ |a| + |t| := by
      dsimp [z]
      calc
        ‖(a : ℂ) + (t : ℂ) * Complex.I‖ ≤
          ‖(a : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |a| + |t| := by simp
    have hval := hC (ξ * z)
    rw [← regularExterior_rotated_potential_eq F s ξ hξ z,
      norm_mul, hξ, one_mul] at hval
    change f t ≤ B
    dsimp [B]
    linarith
  obtain ⟨ell, E, hE, hbelow, habove⟩ :=
    regularExterior_vertical_threshold_candidate F hc hs0 hs1 ξ hξ a h hh0
  have hEfin : volume E ≠ ∞ := by rw [hE.2.2]; finiteness
  have hEreal : volume.real E = 2 * h := by
    rw [Measure.real_def, hE.2.2, ENNReal.toReal_ofReal (by linarith)]
  have hell : B < ell := by
    by_contra hn
    have hBle : ell ≤ B := le_of_not_gt hn
    have hET : E ⊆ Icc (-T) T := by
      intro t ht
      have hft : f t ≤ ell := habove ht
      have hnot : ¬ T ≤ |t| := by
        intro htT
        have hlarge := hT a t htT
        change B < f t at hlarge
        linarith
      exact abs_le.mp (le_of_lt (lt_of_not_ge hnot))
    have hmass := measureReal_mono hET (by rw [Real.volume_Icc]; finiteness)
    have hJreal : volume.real (Icc (-T) T) = 2 * T := by
      rw [Measure.real_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [hEreal, hJreal] at hmass
    dsimp [H] at hh
    linarith
  have hcore : Icc (-L) L ⊆ E := by
    intro t ht
    exact hbelow (lt_of_le_of_lt (hcorebound t ht) hell)
  have hminimal : (∫ t in E, regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
      sInf (regularVerticalCosts F s ξ a h) := by
    have hmin : ∀ D ∈ verticalFeasible h,
        (∫ t in E, f t) ≤ ∫ t in D, f t := by
      intro D hD
      apply threshold_candidate_integral_le f ell E D
        hE.1 hD.1
      · rw [hE.2.2]; finiteness
      · rw [hD.2.2]; finiteness
      · rw [hE.2.2, hD.2.2]
      · exact hbelow
      · exact habove
      · exact regularExterior_vertical_cost_integrableOn
          F hc hs0 hs1 ξ hξ a h E hE
      · exact regularExterior_vertical_cost_integrableOn
          F hc hs0 hs1 ξ hξ a h D hD
    apply le_antisymm
    · apply le_csInf
      · exact ⟨∫ t in E, f t, E, hE, rfl⟩
      · rintro x ⟨D, hD, rfl⟩
        exact hmin D hD
    · exact csInf_le (regularVerticalCosts_bddBelow F hc hs0 hs1 ξ hξ a h)
        ⟨E, hE, rfl⟩
  exact ⟨E, hE, hcore, hminimal⟩

end SpringerLean
