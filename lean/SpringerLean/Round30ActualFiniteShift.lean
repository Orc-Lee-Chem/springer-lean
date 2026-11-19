import SpringerLean.Round30CompensatedFiniteShift
import SpringerLean.Round28PotentialUniformStrip
import SpringerLean.Round28ComparisonHeight

open MeasureTheory Set

namespace SpringerLean

/-- For the actual boundary and segment logarithmic potentials, the translated
finite-window complement identity holds with only the paper's map class. -/
theorem regularExterior_actual_finite_complements_shift
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (x h T ε : ℝ)
    (hh : 0 < h) (hT : h ≤ T)
    (E : Set ℝ) (hEm : MeasurableSet E) (hES : E ⊆ Icc (-T) T) :
    (∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ x t) +
      (∫ t in Icc (-h) h,
        comparisonSegmentPotential ((x : ℂ) + ((t + ε : ℝ) : ℂ) * Complex.I)) -
      (∫ t in E, regularExteriorRotatedPotential F s ξ
        ((x : ℂ) + ((t + ε : ℝ) : ℂ) * Complex.I)) =
    (∫ t in Icc (-T) T \ E, regularExteriorRotatedPotential F s ξ
      ((x : ℂ) + ((t + ε : ℝ) : ℂ) * Complex.I)) -
    (∫ t in Icc (-T) T \ Icc (-h) h,
      comparisonSegmentPotential ((x : ℂ) + ((t + ε : ℝ) : ℂ) * Complex.I)) +
    (∫ t in (Icc (-T) T)ᶜ,
      regularExteriorVerticalPotentialDifference F s ξ x (t + ε)) := by
  let g : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ
    ((x : ℂ) + (t : ℂ) * Complex.I)
  let G : ℝ → ℝ := fun t => comparisonSegmentPotential
    ((x : ℂ) + (t : ℂ) * Complex.I)
  have hS : -T ≤ T := by linarith
  have hIS : Icc (-h) h ⊆ Icc (-T) T := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hd : Integrable (fun t => g t - G t) := by
    change Integrable (regularExteriorVerticalPotentialDifference F s ξ x)
    exact regularExteriorVerticalPotentialDifference_integrable F hc hs0 hs1 ξ x
  have hgInt : IntervalIntegrable (fun t => g (t + ε)) volume (-T) T := by
    apply (IntervalIntegrable.comp_add_right_iff).2
    exact ((regularExterior_rotated_potential_continuous F hc hs0 hs1 ξ hξ).comp
      (by fun_prop : Continuous (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I))).intervalIntegrable _ _
  have hGInt : IntervalIntegrable (fun t => G (t + ε)) volume (-T) T := by
    apply (IntervalIntegrable.comp_add_right_iff).2
    exact comparisonSegmentPotential_vertical_intervalIntegrable
      F hc hs0 hs1 ξ hξ x (-T + ε) (T + ε)
  have hgS : IntegrableOn (fun t => g (t + ε)) (Icc (-T) T) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hS).mp hgInt
  have hGS : IntegrableOn (fun t => G (t + ε)) (Icc (-T) T) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hS).mp hGInt
  have hcomp := compensated_integral_finite_complements_shift
    g G (Icc (-T) T) E (Icc (-h) h) ε
    measurableSet_Icc hEm measurableSet_Icc hES hIS hd hgS hGS
  convert hcomp using 1 <;> rfl

end SpringerLean