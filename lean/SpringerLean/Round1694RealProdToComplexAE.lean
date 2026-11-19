import SpringerLean.Round1691ActualVerticalKnotFlatAE

open MeasureTheory

namespace SpringerLean

/-- Transfer an almost-everywhere assertion from Cartesian product
Lebesgue measure to complex area through the standard real-coordinate
measure equivalence. -/
theorem ae_complex_of_ae_realProd (P : ℂ → Prop)
    (h : ∀ᵐ p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)),
      P (Complex.mk p.1 p.2)) :
    ∀ᵐ z ∂(volume : Measure ℂ), P z := by
  have htarget : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      P (Complex.mk p.1 p.2) := by
    simpa only [Measure.volume_eq_prod ℝ ℝ] using h
  have hcomp : ∀ᵐ z ∂(volume : Measure ℂ),
      P (Complex.mk (Complex.measurableEquivRealProd z).1
        (Complex.measurableEquivRealProd z).2) :=
    Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.tendsto_ae.eventually
      htarget
  filter_upwards [hcomp] with z hz
  simpa [Complex.measurableEquivRealProd_apply] using hz

theorem ae_complex_of_ae_realProd_swapped (P : ℂ → Prop)
    (h : ∀ᵐ p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)),
      P (Complex.mk p.2 p.1)) :
    ∀ᵐ z ∂(volume : Measure ℂ), P z := by
  have hswap : MeasurePreserving Prod.swap
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    Measure.measurePreserving_swap
  have hstandard :
      ∀ᵐ p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)),
        P (Complex.mk p.1 p.2) := by
    have h' := hswap.quasiMeasurePreserving.tendsto_ae.eventually h
    simpa [Prod.swap] using h'
  exact ae_complex_of_ae_realProd P hstandard

end SpringerLean

#print axioms SpringerLean.ae_complex_of_ae_realProd
#print axioms SpringerLean.ae_complex_of_ae_realProd_swapped
