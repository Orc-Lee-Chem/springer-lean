import SpringerLean.Round1710ActualKnotEnergyPointwiseAE
import SpringerLean.Round1681ActualAwayKnotsPointwise

open MeasureTheory

namespace SpringerLean
noncomputable section

/-- The 43 rational endpoint certificates now give the actual
C=25/16 phase-energy estimate almost everywhere on the entire
regular source disk, including positive-area knot level sets. -/
theorem actualHarmonicPhase_pointwise_regular_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ actualMultiplierRegularSet F →
        let U := actualHarmonicPhaseField F k beta
        let p := Real.sqrt
          (((fderiv ℝ U z) (1 : ℂ))^2 +
           ((fderiv ℝ U z) Complex.I)^2)
        let u := U z / ‖actualHarmonic F z‖
        let b := (k : ℝ) / (4 * ((k : ℝ) - 1))
        (k : ℝ)^2 * u^2 + b * actualEnergyFluxDiv F k beta z ≤
          (25 / 16) * p^2 := by
  filter_upwards
    [actualHarmonicPhase_pointwise_knot_ae F hc k hk beta hbeta]
    with z hknot hreg
  obtain ⟨hball, hH, hz0⟩ :=
    (actualMultiplierRegularSet_mem_iff F z).mp hreg
  by_cases hnot : ∀ j : Fin 22,
      actualHarmonicMultiplierTime F k z ≠ energyMultiplierKnotTime j
  · exact actualHarmonicPhase_pointwise_away_knots
      F hc k hk beta hbeta hball hz0 hH hnot
  · push_neg at hnot
    obtain ⟨i, hi⟩ := hnot
    exact hknot i hreg hi

end
end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_pointwise_regular_ae
