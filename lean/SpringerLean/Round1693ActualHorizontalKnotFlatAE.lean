import SpringerLean.Round1686ProductLevelSetWithDerivative
import SpringerLean.Round1689ActualKnotBadSetMeasurable
import SpringerLean.Round1692ActualHorizontalSliceDerivative

open MeasureTheory

namespace SpringerLean

/-- The actual physical multiplier time has horizontal derivative zero
almost everywhere on each fixed knot level, in product coordinates
with the two real coordinates exchanged. -/
theorem actualHarmonicMultiplierTime_horizontal_ae_zero_on_level_swapped
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (c : ℝ) :
    ∀ᵐ p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)),
      Complex.mk p.2 p.1 ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k (Complex.mk p.2 p.1) = c →
      (fderiv ℝ (actualHarmonicMultiplierTime F k)
        (Complex.mk p.2 p.1)) (1 : ℂ) = 0 := by
  let C : ℝ × ℝ → ℂ := fun p => Complex.mk p.2 p.1
  let f : ℝ × ℝ → ℝ := fun p => actualHarmonicMultiplierTime F k (C p)
  let g : ℝ × ℝ → ℝ := fun p =>
    (fderiv ℝ (actualHarmonicMultiplierTime F k) (C p)) (1 : ℂ)
  let S : Set (ℝ × ℝ) := C ⁻¹' actualMultiplierRegularSet F
  have hMk : Measurable (fun p : ℝ × ℝ => Complex.mk p.1 p.2) := by
    convert Complex.measurableEquivRealProd.symm.measurable using 1
    funext p
    exact (Complex.measurableEquivRealProd_symm_apply p).symm
  have hC : Measurable C := by
    convert hMk.comp measurable_swap using 1
    funext p
    rfl
  have hderiv : ∀ p ∈ S,
      DifferentiableAt ℝ (fun v => f (p.1, v)) p.2 ∧
      deriv (fun v => f (p.1, v)) p.2 = g p := by
    intro p hp
    exact ⟨actualHarmonicMultiplierTime_horizontal_differentiableAt
        F hc k p.2 p.1 hp,
      actualHarmonicMultiplierTime_horizontal_deriv F hc k p.2 p.1 hp⟩
  have hMeas : MeasurableSet
      {p : ℝ × ℝ | p ∈ S ∧ f p = c ∧ g p ≠ 0} := by
    change MeasurableSet
      (C ⁻¹' {z : ℂ | z ∈ actualMultiplierRegularSet F ∧
        actualHarmonicMultiplierTime F k z = c ∧
        (fderiv ℝ (actualHarmonicMultiplierTime F k) z) (1 : ℂ) ≠ 0})
    exact (actualHarmonicMultiplierTime_badLevel_measurable
      F hc k c (1 : ℂ)).preimage hC
  exact ae_second_derivative_value_zero_on_level f g c S hderiv hMeas

end SpringerLean

#print axioms SpringerLean.actualHarmonicMultiplierTime_horizontal_ae_zero_on_level_swapped
