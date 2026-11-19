import SpringerLean.Round1686ProductLevelSetWithDerivative
import SpringerLean.Round1689ActualKnotBadSetMeasurable
import SpringerLean.Round1690ComplexCoordinateSliceDerivative

open MeasureTheory

namespace SpringerLean

/-- On every fixed knot level of the ACTUAL physical multiplier time,
its vertical real derivative vanishes almost everywhere on the regular
source region, expressed first in real product coordinates. -/
theorem actualHarmonicMultiplierTime_vertical_ae_zero_on_level
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (c : ℝ) :
    ∀ᵐ p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)),
      Complex.mk p.1 p.2 ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k (Complex.mk p.1 p.2) = c →
      (fderiv ℝ (actualHarmonicMultiplierTime F k)
        (Complex.mk p.1 p.2)) Complex.I = 0 := by
  let C : ℝ × ℝ → ℂ := fun p => Complex.mk p.1 p.2
  let f : ℝ × ℝ → ℝ := fun p => actualHarmonicMultiplierTime F k (C p)
  let g : ℝ × ℝ → ℝ := fun p =>
    (fderiv ℝ (actualHarmonicMultiplierTime F k) (C p)) Complex.I
  let S : Set (ℝ × ℝ) := C ⁻¹' actualMultiplierRegularSet F
  have hC : Measurable C := by
    convert Complex.measurableEquivRealProd.symm.measurable using 1
    funext p
    exact (Complex.measurableEquivRealProd_symm_apply p).symm
  have hderiv : ∀ p ∈ S,
      DifferentiableAt ℝ (fun v => f (p.1, v)) p.2 ∧
      deriv (fun v => f (p.1, v)) p.2 = g p := by
    intro p hp
    exact ⟨actualHarmonicMultiplierTime_vertical_differentiableAt
        F hc k p.1 p.2 hp,
      actualHarmonicMultiplierTime_vertical_deriv F hc k p.1 p.2 hp⟩
  have hMeas : MeasurableSet
      {p : ℝ × ℝ | p ∈ S ∧ f p = c ∧ g p ≠ 0} := by
    change MeasurableSet
      (C ⁻¹' {z : ℂ | z ∈ actualMultiplierRegularSet F ∧
        actualHarmonicMultiplierTime F k z = c ∧
        (fderiv ℝ (actualHarmonicMultiplierTime F k) z) Complex.I ≠ 0})
    exact (actualHarmonicMultiplierTime_badLevel_measurable
      F hc k c Complex.I).preimage hC
  exact ae_second_derivative_value_zero_on_level f g c S hderiv hMeas

end SpringerLean

#print axioms SpringerLean.actualHarmonicMultiplierTime_vertical_ae_zero_on_level
