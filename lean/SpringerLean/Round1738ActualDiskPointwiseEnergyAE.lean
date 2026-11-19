import SpringerLean.Round1737ActualCombinedDivergenceAE
import SpringerLean.Round1711ActualRegularEnergyPointwiseAE
import SpringerLean.Round1712PhaseFieldAtFillingZero

open MeasureTheory

namespace SpringerLean

/-- The actual pointwise energy inequality is now stated on the whole
source disk, with the zero-extended potential and the Cartesian
divergence of the one combined flux. No exceptional filling zero or
multiplier knot level is removed from the domain. -/
theorem actualHarmonicPhase_pointwise_disk_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ‖z‖ < 1 →
      (k : ℝ)^2 * actualHarmonicPhasePotentialDensity F k beta z +
        (k : ℝ) / (4 * ((k : ℝ) - 1)) *
          actualCartesianDiv (actualEnergyFluxField F k beta) z ≤
        (25 / 16 : ℝ) *
          (((fderiv ℝ (actualHarmonicPhaseField F k beta) z) (1 : ℂ))^2 +
           ((fderiv ℝ (actualHarmonicPhaseField F k beta) z) Complex.I)^2) := by
  filter_upwards
    [actualHarmonicPhase_pointwise_regular_ae F hc k hk beta hbeta,
     actualCartesianDiv_actualEnergyFluxField_eq_regular_ae F hc k beta]
    with z hp hdiv hz
  by_cases hH : actualHarmonic F z = 0
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨hU, hUd⟩ :=
      actualHarmonicPhaseField_zero_and_fderiv_zero
        F hc k hk2 beta hz hH
    have hJ := actualCartesianDiv_actualEnergyFluxField_zero_at_filling_zero
      F hc k hk2 beta hbeta hz hH
    simp [actualHarmonicPhasePotentialDensity, hH, hU, hUd, hJ]
  · have hz0 : z ≠ 0 := by
      intro heq
      subst z
      apply hH
      simp [actualHarmonic, exteriorForwardGerm_zero]
    have hreg : z ∈ actualMultiplierRegularSet F :=
      (actualMultiplierRegularSet_mem_iff F z).mpr ⟨hz, hH, hz0⟩
    have hp' := hp hreg
    have hdiv' := hdiv hreg
    rw [← hdiv'] at hp'
    simpa only [actualHarmonicPhasePotentialDensity, div_pow,
      Real.sq_sqrt (by positivity :
        0 ≤ (((fderiv ℝ (actualHarmonicPhaseField F k beta) z)
          (1 : ℂ))^2 +
          ((fderiv ℝ (actualHarmonicPhaseField F k beta) z)
          Complex.I)^2))] using hp'

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_pointwise_disk_ae
