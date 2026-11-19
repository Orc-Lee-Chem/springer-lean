import SpringerLean.Round1702ActualKnotSlopeChainRuleAE
import SpringerLean.Round1668ActualCombinedFluxDefinitions

open MeasureTheory

namespace SpringerLean

/-- The actual phase-gradient flux has its ordinary product-rule
divergence almost everywhere on every physical knot level. The
gradient of the chi multiplier is zero there. -/
theorem actualEnergyFluxPdiv_knot_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ∀ i : Fin 22,
        z ∈ actualMultiplierRegularSet F →
        actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
        let U := actualHarmonicPhaseField F k beta
        let chi := energyMultiplierChi
          (actualHarmonicMultiplierTime F k z)
        actualEnergyFluxPdiv F k beta z =
          chi * (((fderiv ℝ U z) (1 : ℂ))^2 +
            ((fderiv ℝ U z) Complex.I)^2) +
          chi * U z * actualHarmonicPhaseLaplacian F k beta z := by
  filter_upwards
    [actualHarmonicMultiplier_all_knot_hasFDerivAt_zero_ae F hc k]
    with z hz i hreg hlevel
  obtain ⟨hball, _, _⟩ :=
    (actualMultiplierRegularSet_mem_iff F z).mp hreg
  have hchi := (hz i hreg hlevel).1
  have hP := actualHarmonic_phaseFluxP_divergence
    F hc k beta
    (fun w => energyMultiplierChi (actualHarmonicMultiplierTime F k w))
    hball hchi.differentiableAt
  dsimp only at hP
  simp only [actualEnergyFluxPdiv, hchi.fderiv, ContinuousLinearMap.zero_apply,
    zero_mul, add_zero, mul_zero] at hP ⊢
  exact hP

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxPdiv_knot_ae
