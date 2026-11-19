import SpringerLean.Round1698FiniteRampSumLipschitz

open MeasureTheory

namespace SpringerLean

/-- A Lipschitz scalar multiplier of the actual physical time has
zero real fderiv almost everywhere on any one of its knot levels.
No nullity assumption on the knot level is made. -/
theorem actualHarmonicMultiplier_comp_ae_fderiv_zero_on_level
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (c : ℝ) (φ : ℝ → ℝ) {C : NNReal}
    (hφ : LipschitzWith C φ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = c →
      fderiv ℝ (fun w => φ (actualHarmonicMultiplierTime F k w)) z = 0 := by
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
  exact (lipschitz_comp_hasFDerivAt_zero
    (actualHarmonicMultiplierTime F k) φ z ht0 hφ).fderiv

theorem actualHarmonicMultiplierChi_ae_fderiv_zero_on_knot
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (i : Fin 22) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
      fderiv ℝ (fun w => energyMultiplierChi
        (actualHarmonicMultiplierTime F k w)) z = 0 :=
  actualHarmonicMultiplier_comp_ae_fderiv_zero_on_level
    F hc k (energyMultiplierKnotTime i)
    energyMultiplierChi energyMultiplierChi_lipschitz

theorem actualHarmonicMultiplierF_ae_fderiv_zero_on_knot
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (i : Fin 22) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
      fderiv ℝ (fun w => energyMultiplierF
        (actualHarmonicMultiplierTime F k w)) z = 0 :=
  actualHarmonicMultiplier_comp_ae_fderiv_zero_on_level
    F hc k (energyMultiplierKnotTime i)
    energyMultiplierF energyMultiplierF_lipschitz

theorem actualHarmonicMultiplierSigma_ae_fderiv_zero_on_knot
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (i : Fin 22) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
      fderiv ℝ (fun w => energyMultiplierSigma
        (actualHarmonicMultiplierTime F k w)) z = 0 :=
  actualHarmonicMultiplier_comp_ae_fderiv_zero_on_level
    F hc k (energyMultiplierKnotTime i)
    energyMultiplierSigma energyMultiplierSigma_lipschitz

end SpringerLean

#print axioms SpringerLean.actualHarmonicMultiplier_comp_ae_fderiv_zero_on_level
#print axioms SpringerLean.actualHarmonicMultiplierChi_ae_fderiv_zero_on_knot
#print axioms SpringerLean.actualHarmonicMultiplierF_ae_fderiv_zero_on_knot
#print axioms SpringerLean.actualHarmonicMultiplierSigma_ae_fderiv_zero_on_knot
