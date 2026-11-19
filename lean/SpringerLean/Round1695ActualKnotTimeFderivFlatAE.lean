import SpringerLean.Round1691ActualVerticalKnotFlatAE
import SpringerLean.Round1693ActualHorizontalKnotFlatAE
import SpringerLean.Round1694RealProdToComplexAE

open MeasureTheory

namespace SpringerLean

/-- On each fixed multiplier knot level, the full real fderiv of the
ACTUAL physical multiplier time is zero almost everywhere on its
regular complex source region. The level itself may have positive
area; the proof uses both coordinate slices and Fubini. -/
theorem actualHarmonicMultiplierTime_ae_fderiv_zero_on_level
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (c : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = c →
      fderiv ℝ (actualHarmonicMultiplierTime F k) z = 0 := by
  have hV : ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = c →
      (fderiv ℝ (actualHarmonicMultiplierTime F k) z) Complex.I = 0 :=
    ae_complex_of_ae_realProd _
      (actualHarmonicMultiplierTime_vertical_ae_zero_on_level F hc k c)
  have hH : ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = c →
      (fderiv ℝ (actualHarmonicMultiplierTime F k) z) (1 : ℂ) = 0 :=
    ae_complex_of_ae_realProd_swapped _
      (actualHarmonicMultiplierTime_horizontal_ae_zero_on_level_swapped F hc k c)
  filter_upwards [hV, hH] with z hv hh hz ht
  have hI := hv hz ht
  have h1 := hh hz ht
  ext w
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hw, map_add, map_smul, map_smul, h1, hI]
  simp

end SpringerLean

#print axioms SpringerLean.actualHarmonicMultiplierTime_ae_fderiv_zero_on_level
