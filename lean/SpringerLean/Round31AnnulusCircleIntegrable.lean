import SpringerLean.Round30AnnulusSubmean

open MeasureTheory Set Metric Filter

namespace SpringerLean

/-- The finite-annulus compensated potential is genuinely integrable on the
circle; the circle average in the finite-annulus submean is not a default value. -/
theorem regularExterior_vertical_difference_finite_annulus_circleIntegrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (a T M ρ : ℝ) (hρ : 0 < ρ) (hρT : ρ < T) :
    CircleIntegrable
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
  have hgci := regularExterior_rotated_potential_vertical_set_circleIntegrable
    F hc hs0 hs1 ξ hξ A hAm hAb (a : ℂ) ρ
  have hGci := comparisonSegmentPotential_vertical_set_circleIntegrable_of_sep
    A hAm hAb a T ρ hρ.le hρT hsep
  have hdiff : CircleIntegrable
      (fun z : ℂ =>
        (∫ t in A, regularExteriorRotatedPotential F s ξ
          (z + (t : ℂ) * Complex.I)) -
        (∫ t in A, comparisonSegmentPotential
          (z + (t : ℂ) * Complex.I))) (a : ℂ) ρ :=
    hgci.sub hGci
  apply CircleIntegrable.congr_codiscreteWithin ?_ hdiff
  filter_upwards [self_mem_codiscreteWithin (sphere (a : ℂ) |ρ|)] with z hz
  have hrad : ‖z - (a : ℂ)‖ = ρ := by
    simpa [mem_sphere, dist_eq_norm, abs_of_pos hρ] using hz
  have him : |z.im| ≤ ρ := by
    have h := Complex.abs_im_le_norm (z - (a : ℂ))
    simpa [Complex.sub_im, hrad] using h
  exact (regularExterior_vertical_difference_setIntegral_eq_sub_of_sep
    F hc hs0 hs1 ξ hξ A hAm hAb z T ρ hρ.le hρT him hsep).symm

end SpringerLean