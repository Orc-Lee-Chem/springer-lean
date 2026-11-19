import SpringerLean.Round1736ActualRSFluxDifferentiability

open MeasureTheory

namespace SpringerLean

/-- The divergence of the actual signed Cartesian flux equals the
already checked P/R/S ledger almost everywhere on the regular source
region, including every physical multiplier knot level. -/
theorem actualCartesianDiv_actualEnergyFluxField_eq_regular_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ actualMultiplierRegularSet F →
      actualCartesianDiv (actualEnergyFluxField F k beta) z =
        actualEnergyFluxDiv F k beta z := by
  filter_upwards
    [actualEnergyMultiplier_compositions_differentiableAt_regular_ae
      F hc k]
    with z hm hreg
  obtain ⟨hball, hH, hz0⟩ :=
    (actualMultiplierRegularSet_mem_iff F z).mp hreg
  obtain ⟨hchi, hphi, hsigma⟩ := hm hreg
  exact actualCartesianDiv_actualEnergyFluxField_eq F k beta z
    (actualEnergyFluxPField_differentiableAt_regular
      F hc k beta hball hchi)
    (actualEnergyFluxRField_differentiableAt_regular
      F hc k beta hball hz0 hH hphi)
    (actualEnergyFluxSField_differentiableAt_regular
      F hc k beta hball hH hsigma)

end SpringerLean

#print axioms SpringerLean.actualCartesianDiv_actualEnergyFluxField_eq_regular_ae
