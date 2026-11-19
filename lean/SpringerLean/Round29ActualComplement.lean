import SpringerLean.Round29AuxComplement

open MeasureTheory Set

namespace SpringerLean

/-- At any actual minimizing set, the auxiliary is controlled only by the
reference errors outside that set and the centered comparison interval. -/
theorem regularVerticalAuxiliary_le_reference_complement_errors
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h)
    (E : Set ℝ) (hE : E ∈ verticalFeasible h)
    (hmin : (∫ t in E, regularExteriorRotatedPotential F s ξ
      ((a : ℂ) + (t : ℂ) * Complex.I)) =
        sInf (regularVerticalCosts F s ξ a h)) :
    regularVerticalAuxiliary F s ξ a h ≤
      (∫ t in Eᶜ,
        |regularExteriorRotatedPotential F s ξ
           ((a : ℂ) + (t : ℂ) * Complex.I) - verticalReferenceKernel a t|) +
      (∫ t in (Icc (-h) h)ᶜ,
        |comparisonSegmentPotential
           ((a : ℂ) + (t : ℂ) * Complex.I) - verticalReferenceKernel a t|) := by
  let I : Set ℝ := Icc (-h) h
  let g : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ
    ((a : ℂ) + (t : ℂ) * Complex.I)
  let G : ℝ → ℝ := fun t => comparisonSegmentPotential
    ((a : ℂ) + (t : ℂ) * Complex.I)
  let k : ℝ → ℝ := verticalReferenceKernel a
  have hI : MeasurableSet I := measurableSet_Icc
  have hkI : IntegrableOn k I := (verticalReferenceKernel_continuous a).integrableOn_Icc
  obtain ⟨T, hT⟩ := isBounded_iff_forall_norm_le.mp hE.2.1
  have hET : E ⊆ Icc (-T) T := by
    intro t ht
    have htT : |t| ≤ T := by simpa [Real.norm_eq_abs] using hT t ht
    exact abs_le.mp htT
  have hkE : IntegrableOn k E :=
    ((verticalReferenceKernel_continuous a).integrableOn_Icc).mono_set hET
  have herr := regularExterior_reference_vertical_errors_integrable
    F hc hs0 hs1 ξ hξ a
  have hkmin := verticalReferenceKernel_centered_interval_minimizes a h hh.le E hE
  have hbound := compensated_auxiliary_le_reference_complement_errors
    g G k E I hE.1 hI herr.1 herr.2 hkE hkI hkmin
  simp only [regularVerticalAuxiliary, not_le.mpr hh, ↓reduceIte]
  rw [← hmin]
  simpa only [g, G, k, I, regularExteriorVerticalPotentialDifference,
    regularExteriorRotatedPotential, comparisonSegmentPotential] using hbound

end SpringerLean
