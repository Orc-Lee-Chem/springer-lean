import SpringerLean.Round1704ActualKnotRFluxAE
import SpringerLean.Round1605ActualPhaseFluxS

open scoped ComplexConjugate
open MeasureTheory

namespace SpringerLean

/-- On every physical knot level the actual drift-flux multiplier is
differentiable almost everywhere, and its gradient term vanishes. -/
theorem actualEnergyFluxSdiv_knot_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ∀ i : Fin 22,
        z ∈ actualMultiplierRegularSet F →
        actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
        let U := actualHarmonicPhaseField F k beta
        let sigma := energyMultiplierSigma
          (actualHarmonicMultiplierTime F k z)
        let Q := (conj (actualHarmonic F z))⁻¹
        actualEnergyFluxSdiv F k beta z =
          2 * sigma * U z *
            (Q.re * (fderiv ℝ U z) (1 : ℂ) +
             Q.im * (fderiv ℝ U z) Complex.I) -
          2 * sigma * (U z)^2 *
            (deriv (exteriorForwardGerm F) (conj z) /
              (actualHarmonic F z)^2).re := by
  filter_upwards
    [actualHarmonicMultiplier_all_knot_hasFDerivAt_zero_ae F hc k]
    with z hz i hreg hlevel
  obtain ⟨hball, hH, _⟩ :=
    (actualMultiplierRegularSet_mem_iff F z).mp hreg
  have hs := (hz i hreg hlevel).2.2
  have hS := actualHarmonic_phaseFluxS_divergence
    F hc k beta
    (fun w => energyMultiplierSigma (actualHarmonicMultiplierTime F k w))
    hball hH hs.differentiableAt
  dsimp only at hS
  simp only [actualEnergyFluxSdiv, hs.fderiv, zero_apply,
    zero_mul, add_zero, mul_zero, sub_zero] at hS ⊢
  convert hS using 1 <;> ring

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxSdiv_knot_ae
