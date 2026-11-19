import SpringerLean.Round1701ActualKnotMultiplierHasFDerivAE

open MeasureTheory

namespace SpringerLean

/-- At any actual physical knot, the printed one-sided slope chain rules
hold almost everywhere. Both sides vanish there, so no measure-zero
assumption about the knot level is needed. -/
theorem actualHarmonicMultiplier_all_knot_slope_chain_rules_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (k : ℕ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ∀ i : Fin 22,
        z ∈ actualMultiplierRegularSet F →
        actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
        let row := energyMultiplierEndpointRaw
          (⟨2 * i.val, by omega⟩ : Fin 43)
        fderiv ℝ (fun w => energyMultiplierChi
          (actualHarmonicMultiplierTime F k w)) z =
          (row.cp : ℝ) • fderiv ℝ (actualHarmonicMultiplierTime F k) z ∧
        fderiv ℝ (fun w => energyMultiplierF
          (actualHarmonicMultiplierTime F k w)) z =
          (row.fp : ℝ) • fderiv ℝ (actualHarmonicMultiplierTime F k) z ∧
        fderiv ℝ (fun w => energyMultiplierSigma
          (actualHarmonicMultiplierTime F k w)) z =
          (row.sp : ℝ) • fderiv ℝ (actualHarmonicMultiplierTime F k) z := by
  have htime : ∀ᵐ z ∂(volume : Measure ℂ), ∀ i : Fin 22,
      z ∈ actualMultiplierRegularSet F →
      actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
      fderiv ℝ (actualHarmonicMultiplierTime F k) z = 0 :=
    ae_all_iff.mpr (fun i =>
      actualHarmonicMultiplierTime_ae_fderiv_zero_on_level
        F hc k (energyMultiplierKnotTime i))
  filter_upwards
    [actualHarmonicMultiplier_all_knot_hasFDerivAt_zero_ae F hc k,
      htime] with z hcomp ht i hreg hlevel
  obtain ⟨hchi, hf, hs⟩ := hcomp i hreg hlevel
  have ht0 := ht i hreg hlevel
  simp [hchi.fderiv, hf.fderiv, hs.fderiv, ht0]

end SpringerLean

#print axioms SpringerLean.actualHarmonicMultiplier_all_knot_slope_chain_rules_ae
