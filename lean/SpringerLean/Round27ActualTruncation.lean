import SpringerLean.Round27CompensatedTruncation

open MeasureTheory Set

namespace SpringerLean

/-- The actual auxiliary value on a finite vertical window, with the
whole-line tail kept as a single compensated difference. This is the exact
form of the BLP complement-set identity before sending the window outward. -/
theorem regularVerticalAuxiliary_finite_complements_of_minimizer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h)
    (E : Set ℝ) (hE : E ∈ verticalFeasible h)
    (hmin : (∫ t in E, regularExteriorRotatedPotential F s ξ
      ((a : ℂ) + (t : ℂ) * Complex.I)) =
        sInf (regularVerticalCosts F s ξ a h))
    (T : ℝ) (hT : h ≤ T) (hES : E ⊆ Icc (-T) T) :
    regularVerticalAuxiliary F s ξ a h =
      (∫ t in Icc (-T) T \ E,
        regularExteriorRotatedPotential F s ξ
          ((a : ℂ) + (t : ℂ) * Complex.I)) -
      (∫ t in Icc (-T) T \ Icc (-h) h,
        comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I)) +
      (∫ t in (Icc (-T) T)ᶜ,
        regularExteriorVerticalPotentialDifference F s ξ a t) := by
  let g : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ
    ((a : ℂ) + (t : ℂ) * Complex.I)
  let G : ℝ → ℝ := fun t => comparisonSegmentPotential
    ((a : ℂ) + (t : ℂ) * Complex.I)
  let S : Set ℝ := Icc (-T) T
  let I : Set ℝ := Icc (-h) h
  have hIS : I ⊆ S := by
    intro t ht
    change -h ≤ t ∧ t ≤ h at ht
    change -T ≤ t ∧ t ≤ T
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hgS : IntegrableOn g S :=
    regularExterior_vertical_cost_integrableOn F hc hs0 hs1 ξ hξ a T S
      (by simpa [S] using centered_interval_verticalFeasible T 0)
  have hd : Integrable (fun t => g t - G t) := by
    have hfun : (fun t => g t - G t) =
        regularExteriorVerticalPotentialDifference F s ξ a := by rfl
    rw [hfun]
    exact regularExteriorVerticalPotentialDifference_integrable F hc hs0 hs1 ξ a
  have hGS : IntegrableOn G S := by
    have h := hgS.sub hd.integrableOn
    convert h using 1
    funext t
    change G t = g t - (g t - G t)
    ring
  have halg := compensated_integral_finite_complements
    g G S E I measurableSet_Icc hE.1 measurableSet_Icc
    hES hIS hd hgS hGS
  simp only [regularVerticalAuxiliary, not_le.mpr hh, reduceIte]
  rw [← hmin]
  simpa only [g, G, S, I, regularExteriorVerticalPotentialDifference,
    regularExteriorRotatedPotential, comparisonSegmentPotential] using halg


/-- Every actual positive-height auxiliary value has a genuine minimizing
set and a finite window on which the complement decomposition is exact.
The sole whole-line term is the integrable compensated difference. -/
theorem regularVerticalAuxiliary_exists_finite_complement_representation
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h) :
    ∃ E ∈ verticalFeasible h, ∃ T : ℝ, h ≤ T ∧ E ⊆ Icc (-T) T ∧
      regularVerticalAuxiliary F s ξ a h =
        (∫ t in Icc (-T) T \ E,
          regularExteriorRotatedPotential F s ξ
            ((a : ℂ) + (t : ℂ) * Complex.I)) -
        (∫ t in Icc (-T) T \ Icc (-h) h,
          comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I)) +
        (∫ t in (Icc (-T) T)ᶜ,
          regularExteriorVerticalPotentialDifference F s ξ a t) := by
  obtain ⟨E, hE, hmin⟩ :=
    regularVerticalCosts_exists_minimizer F hc hs0 hs1 ξ hξ a h hh
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp hE.2.1
  let T : ℝ := max h B
  have hT : h ≤ T := le_max_left _ _
  have hBT : B ≤ T := le_max_right _ _
  have hES : E ⊆ Icc (-T) T := by
    intro t ht
    have htB : |t| ≤ B := by simpa [Real.norm_eq_abs] using hB t ht
    have htBounds := abs_le.mp htB
    exact ⟨by linarith [htBounds.1], by linarith [htBounds.2]⟩
  refine ⟨E, hE, T, hT, hES, ?_⟩
  exact regularVerticalAuxiliary_finite_complements_of_minimizer
    F hc hs0 hs1 ξ hξ a h hh E hE hmin T hT hES
end SpringerLean