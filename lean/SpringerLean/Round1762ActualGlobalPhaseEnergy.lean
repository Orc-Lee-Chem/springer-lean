import SpringerLean.Round1761ActualCutoffDivergenceIntegral
import SpringerLean.Round1747ActualCutoffEnergyReduction

open Filter
open scoped Topology

namespace SpringerLean

/-- The actual global phase-energy inequality from the original
exterior-univalent class, for every k>=751 and every unit phase. -/
theorem actualHarmonicPhase_energy_le_twentyfive_sixteenths
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1) :
    (k : ℝ)^2 * actualHarmonicPhasePotential F k beta ≤
      (25 / 16 : ℝ) * actualHarmonicPhaseEnergy F k beta := by
  let ε : ℕ → ℝ := fun j => 1/((j : ℝ)+2)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hε1 (j : ℕ) : ε j < 1 := by
    dsimp [ε]
    apply (div_lt_one (by positivity : (0 : ℝ) < (j : ℝ)+2)).mpr
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 2))
  have hparts (j : ℕ) := actualEnergyFlux_cutoff_integration_by_parts
    F hc k (by omega : 2 ≤ k) beta hbeta (hε j) (hε1 j)
  exact actualHarmonicPhaseEnergy_of_cutoff_flux_balance
    F hc k hk beta hbeta ε hε hlim
    (fun j => (hparts j).1) (fun j => (hparts j).2)

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_energy_le_twentyfive_sixteenths
