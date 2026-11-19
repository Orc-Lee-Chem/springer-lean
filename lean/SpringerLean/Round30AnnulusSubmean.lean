import SpringerLean.Round30AnnulusDifference

open MeasureTheory Set Metric

namespace SpringerLean

/-- The actual compensated potential integrated over a finite outer annulus
satisfies the circle submean; only the unbounded tail remains to pass to. -/
theorem regularExterior_vertical_difference_finite_annulus_submean
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (a T M ρ : ℝ) (hρ : 0 < ρ) (hρT : ρ < T) (hTM : T ≤ M) :
    (∫ t in Icc (-M) M \ Icc (-T) T,
      regularExteriorVerticalPotentialDifference F s ξ a t) ≤
    Real.circleAverage
      (fun z : ℂ => ∫ t in Icc (-M) M \ Icc (-T) T,
        regularExteriorVerticalPotentialDifference F s ξ z.re (t + z.im))
      (a : ℂ) ρ := by
  let A : Set ℝ := Icc (-M) M \ Icc (-T) T
  have hAm : MeasurableSet A := measurableSet_Icc.diff measurableSet_Icc
  have hAb : Bornology.IsBounded A :=
    (isBounded_Icc (-M) M).subset diff_subset
  have hsep : ∀ t ∈ A, T ≤ |t| := by
    intro t ht
    have hnot : t ∉ Icc (-T) T := ht.2
    by_cases hneg : t < -T
    · rw [abs_of_neg (by linarith)]
      linarith
    · have hpos : T < t := by
        by_contra hn
        apply hnot
        exact ⟨by linarith, by linarith⟩
      rw [abs_of_pos (by linarith)]
      linarith
  have hTpos : 0 < T := lt_trans hρ hρT
  have hES : Icc (-T) T ⊆ Icc (-M) M := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hbounded := regularExterior_finite_complement_bounded_part_submean
    F hc hs0 hs1 ξ hξ (Icc (-T) T) measurableSet_Icc
      (isBounded_Icc (-T) T) a T M ρ hTpos hTM hES hρ hρT
  have hcenter := regularExterior_vertical_difference_setIntegral_eq_sub_of_sep
    F hc hs0 hs1 ξ hξ A hAm hAb (a : ℂ) T ρ hρ.le hρT
      (by simpa using hρ.le) hsep
  have hcircle :
      Real.circleAverage
        (fun z : ℂ => ∫ t in A,
          regularExteriorVerticalPotentialDifference F s ξ z.re (t + z.im))
        (a : ℂ) ρ =
      Real.circleAverage
        (fun z : ℂ =>
          (∫ t in A, regularExteriorRotatedPotential F s ξ
            (z + (t : ℂ) * Complex.I)) -
          (∫ t in A, comparisonSegmentPotential
            (z + (t : ℂ) * Complex.I)))
        (a : ℂ) ρ := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hrad : ‖z - (a : ℂ)‖ = ρ := by
      simpa [mem_sphere, dist_eq_norm, abs_of_pos hρ] using hz
    have him : |z.im| ≤ ρ := by
      have h := Complex.abs_im_le_norm (z - (a : ℂ))
      simpa [Complex.sub_im, hrad] using h
    exact regularExterior_vertical_difference_setIntegral_eq_sub_of_sep
      F hc hs0 hs1 ξ hξ A hAm hAb z T ρ hρ.le hρT him hsep
  change (∫ t in A,
      regularExteriorVerticalPotentialDifference F s ξ a t) ≤
    Real.circleAverage
      (fun z : ℂ => ∫ t in A,
        regularExteriorVerticalPotentialDifference F s ξ z.re (t + z.im))
      (a : ℂ) ρ
  simp only [Complex.ofReal_re, Complex.ofReal_im, add_zero] at hcenter
  rw [hcenter, hcircle]
  exact hbounded

end SpringerLean