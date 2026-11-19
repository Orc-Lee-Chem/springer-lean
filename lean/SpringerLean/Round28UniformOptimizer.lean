import SpringerLean.Round28WindowMeasure

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

namespace SpringerLean

/-- All actual positive-height vertical cost problems over a compact
parameter rectangle admit threshold minimizers inside one common finite
vertical window. The window depends on the rectangle, not on its point. -/
theorem regularVerticalCosts_exists_minimizer_uniform_window
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ (a h : ℝ), |a| ≤ A → 0 < h → h ≤ H →
      ∃ E ∈ verticalFeasible h,
        E ⊆ Icc (-T) T ∧
        (∫ t in E, regularExteriorRotatedPotential F s ξ
          ((a : ℂ) + (t : ℂ) * Complex.I)) =
          sInf (regularVerticalCosts F s ξ a h) := by
  obtain ⟨C, hC0, hC⟩ :=
    regularExterior_boundary_potential_linear_bound F hc hs0 hs1
  let B : ℝ := A + H + C + 2
  let J : Set ℝ := Icc (-(H + 1)) (H + 1)
  obtain ⟨T, hT0, hT⟩ :=
    regularExterior_rotated_potential_vertical_uniform_coercive
      F hc hs0 hs1 ξ hξ B
  refine ⟨T, hT0, ?_⟩
  intro a h ha hh hHh
  let f : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ
    ((a : ℂ) + (t : ℂ) * Complex.I)
  have hJbound : ∀ t ∈ J, f t ≤ B := by
    intro t ht
    have htab : |t| ≤ H + 1 := by
      exact abs_le.mpr (by simpa only [J, mem_Icc] using ht)
    let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
    have hzbound : ‖ξ * z‖ ≤ A + H + 1 := by
      rw [norm_mul, hξ, one_mul]
      have htri : ‖z‖ ≤ |a| + |t| := by
        dsimp [z]
        calc
          ‖(a : ℂ) + (t : ℂ) * Complex.I‖ ≤
            ‖(a : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = |a| + |t| := by simp
      linarith
    have hpot := hC (ξ * z)
    rw [← regularExterior_rotated_potential_eq F s ξ hξ z] at hpot
    change f t ≤ B
    dsimp [B]
    linarith
  obtain ⟨ell, E, hE, hbelow, habove⟩ :=
    regularExterior_vertical_threshold_candidate
      F hc hs0 hs1 ξ hξ a h hh
  have hEfin : volume E ≠ ∞ := by
    rw [hE.2.2]
    finiteness
  have hEreal : volume.real E = 2 * h := by
    rw [Measure.real_def, hE.2.2, ENNReal.toReal_ofReal (by linarith)]
  have hJreal : volume.real J = 2 * (H + 1) := by
    dsimp [J]
    rw [Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  have hmass : volume.real E < volume.real J := by
    rw [hEreal, hJreal]
    linarith
  have hell : ell ≤ B :=
    threshold_le_of_large_bounded_test f ell B E J hbelow hJbound hEfin hmass
  have hES : E ⊆ Icc (-T) T := by
    intro t ht
    have hft : f t ≤ ell := habove ht
    have hnot : ¬ T ≤ |t| := by
      intro htT
      have hbig := hT a t htT
      dsimp [f] at hft
      linarith
    have htlt : |t| < T := lt_of_not_ge hnot
    exact abs_le.mp htlt.le
  have hminimal : ∀ D ∈ verticalFeasible h,
      (∫ t in E, f t) ≤ ∫ t in D, f t := by
    intro D hD
    apply threshold_candidate_integral_le f ell E D
    · exact hE.1
    · exact hD.1
    · exact hEfin
    · rw [hD.2.2]
      finiteness
    · rw [hE.2.2, hD.2.2]
    · exact hbelow
    · exact habove
    · exact regularExterior_vertical_cost_integrableOn
        F hc hs0 hs1 ξ hξ a h E hE
    · exact regularExterior_vertical_cost_integrableOn
        F hc hs0 hs1 ξ hξ a h D hD
  refine ⟨E, hE, hES, ?_⟩
  change (∫ t in E, f t) = sInf (regularVerticalCosts F s ξ a h)
  apply le_antisymm
  · apply le_csInf (regularVerticalCosts_nonempty F s ξ a h)
    rintro q ⟨D, hD, rfl⟩
    exact hminimal D hD
  · apply csInf_le (regularVerticalCosts_bddBelow F hc hs0 hs1 ξ hξ a h)
    exact ⟨E, hE, rfl⟩

end SpringerLean