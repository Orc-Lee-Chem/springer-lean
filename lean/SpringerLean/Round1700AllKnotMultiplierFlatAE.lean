import SpringerLean.Round1699ActualKnotMultiplierFlatAE

open MeasureTheory

namespace SpringerLean

/-- A single full-measure set controls all 22 physical knot levels and
all three multiplier compositions at once. -/
theorem actualHarmonicMultiplier_all_knot_compositions_flat_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (k : ℕ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ∀ i : Fin 22,
        z ∈ actualMultiplierRegularSet F →
        actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
        fderiv ℝ (fun w => energyMultiplierChi
          (actualHarmonicMultiplierTime F k w)) z = 0 ∧
        fderiv ℝ (fun w => energyMultiplierF
          (actualHarmonicMultiplierTime F k w)) z = 0 ∧
        fderiv ℝ (fun w => energyMultiplierSigma
          (actualHarmonicMultiplierTime F k w)) z = 0 := by
  have hchi : ∀ᵐ z ∂(volume : Measure ℂ), ∀ i : Fin 22,
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
      fderiv ℝ (fun w => energyMultiplierChi
        (actualHarmonicMultiplierTime F k w)) z = 0 :=
    ae_all_iff.mpr (fun i =>
      actualHarmonicMultiplierChi_ae_fderiv_zero_on_knot F hc k i)
  have hf : ∀ᵐ z ∂(volume : Measure ℂ), ∀ i : Fin 22,
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
      fderiv ℝ (fun w => energyMultiplierF
        (actualHarmonicMultiplierTime F k w)) z = 0 :=
    ae_all_iff.mpr (fun i =>
      actualHarmonicMultiplierF_ae_fderiv_zero_on_knot F hc k i)
  have hs : ∀ᵐ z ∂(volume : Measure ℂ), ∀ i : Fin 22,
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
      fderiv ℝ (fun w => energyMultiplierSigma
        (actualHarmonicMultiplierTime F k w)) z = 0 :=
    ae_all_iff.mpr (fun i =>
      actualHarmonicMultiplierSigma_ae_fderiv_zero_on_knot F hc k i)
  filter_upwards [hchi, hf, hs] with z hχ hF hσ i hz ht
  exact ⟨hχ i hz ht, hF i hz ht, hσ i hz ht⟩

end SpringerLean

#print axioms SpringerLean.actualHarmonicMultiplier_all_knot_compositions_flat_ae
