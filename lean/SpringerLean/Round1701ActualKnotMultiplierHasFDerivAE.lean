import SpringerLean.Round1700AllKnotMultiplierFlatAE

open MeasureTheory

namespace SpringerLean

/-- The full differentiability statement at a physical knot. The
corresponding fderiv is the zero real-linear map. -/
theorem actualHarmonicMultiplier_comp_ae_hasFDerivAt_zero_on_level
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (c : ℝ) (φ : ℝ → ℝ) {C : NNReal}
    (hφ : LipschitzWith C φ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = c →
      HasFDerivAt (fun w => φ (actualHarmonicMultiplierTime F k w))
        (0 : ℂ →L[ℝ] ℝ) z := by
  filter_upwards
    [actualHarmonicMultiplierTime_ae_fderiv_zero_on_level F hc k c]
    with z hz hreg hlevel
  obtain ⟨hball, hH, hz0⟩ :=
    (actualMultiplierRegularSet_mem_iff F z).mp hreg
  have ht : DifferentiableAt ℝ (actualHarmonicMultiplierTime F k) z :=
    actualHarmonicMultiplierTime_differentiableAt F hc k hball hz0 hH
  have ht0 : HasFDerivAt (actualHarmonicMultiplierTime F k)
      (0 : ℂ →L[ℝ] ℝ) z := by
    simpa [hz hreg hlevel] using ht.hasFDerivAt
  exact lipschitz_comp_hasFDerivAt_zero
    (actualHarmonicMultiplierTime F k) φ z ht0 hφ

/-- All three actual physical multipliers are differentiable with
zero derivative at every knot, on one common full-measure set. -/
theorem actualHarmonicMultiplier_all_knot_hasFDerivAt_zero_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (k : ℕ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ∀ i : Fin 22,
        z ∈ actualMultiplierRegularSet F →
        actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
        HasFDerivAt (fun w => energyMultiplierChi
          (actualHarmonicMultiplierTime F k w))
          (0 : ℂ →L[ℝ] ℝ) z ∧
        HasFDerivAt (fun w => energyMultiplierF
          (actualHarmonicMultiplierTime F k w))
          (0 : ℂ →L[ℝ] ℝ) z ∧
        HasFDerivAt (fun w => energyMultiplierSigma
          (actualHarmonicMultiplierTime F k w))
          (0 : ℂ →L[ℝ] ℝ) z := by
  have hchi : ∀ᵐ z ∂(volume : Measure ℂ), ∀ i : Fin 22,
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
      HasFDerivAt (fun w => energyMultiplierChi
        (actualHarmonicMultiplierTime F k w)) (0 : ℂ →L[ℝ] ℝ) z :=
    ae_all_iff.mpr (fun i =>
      actualHarmonicMultiplier_comp_ae_hasFDerivAt_zero_on_level
        F hc k (energyMultiplierKnotTime i)
        energyMultiplierChi energyMultiplierChi_lipschitz)
  have hf : ∀ᵐ z ∂(volume : Measure ℂ), ∀ i : Fin 22,
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
      HasFDerivAt (fun w => energyMultiplierF
        (actualHarmonicMultiplierTime F k w)) (0 : ℂ →L[ℝ] ℝ) z :=
    ae_all_iff.mpr (fun i =>
      actualHarmonicMultiplier_comp_ae_hasFDerivAt_zero_on_level
        F hc k (energyMultiplierKnotTime i)
        energyMultiplierF energyMultiplierF_lipschitz)
  have hs : ∀ᵐ z ∂(volume : Measure ℂ), ∀ i : Fin 22,
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
      HasFDerivAt (fun w => energyMultiplierSigma
        (actualHarmonicMultiplierTime F k w)) (0 : ℂ →L[ℝ] ℝ) z :=
    ae_all_iff.mpr (fun i =>
      actualHarmonicMultiplier_comp_ae_hasFDerivAt_zero_on_level
        F hc k (energyMultiplierKnotTime i)
        energyMultiplierSigma energyMultiplierSigma_lipschitz)
  filter_upwards [hchi, hf, hs] with z hχ hF hσ i hz ht
  exact ⟨hχ i hz ht, hF i hz ht, hσ i hz ht⟩

end SpringerLean

#print axioms SpringerLean.actualHarmonicMultiplier_comp_ae_hasFDerivAt_zero_on_level
#print axioms SpringerLean.actualHarmonicMultiplier_all_knot_hasFDerivAt_zero_ae
