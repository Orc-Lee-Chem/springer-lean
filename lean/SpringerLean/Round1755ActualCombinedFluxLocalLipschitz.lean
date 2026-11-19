import SpringerLean.Round1754ActualFluxZeroLocalLipschitz

open Filter
open scoped Topology

namespace SpringerLean

/-- The physical combined flux is locally Lipschitz on the punctured
source disk. This includes all multiplier levels and all filling
zeros, with the source center reserved for the radial cutoff. -/
theorem actualEnergyFluxField_locally_lipschitz_punctured_disk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    ∃ K : NNReal, ∃ s ∈ 𝓝 z,
      LipschitzOnWith K (actualEnergyFluxField F k beta) s := by
  have hfields :
      (∃ K : NNReal, ∃ s ∈ 𝓝 z,
        LipschitzOnWith K (actualEnergyFluxPField F k beta) s) ∧
      (∃ K : NNReal, ∃ s ∈ 𝓝 z,
        LipschitzOnWith K (actualEnergyFluxRField F k beta) s) ∧
      (∃ K : NNReal, ∃ s ∈ 𝓝 z,
        LipschitzOnWith K (actualEnergyFluxSField F k beta) s) := by
    by_cases hH : actualHarmonic F z = 0
    · exact actualEnergyFluxFields_locally_lipschitz_at_filling_zero
        F hc k hk beta hbeta hz hz0 hH
    · exact actualEnergyFluxFields_locally_lipschitz_regular
        F hc k (by omega) beta hbeta hz hz0 hH
  let P := actualEnergyFluxPField F k beta
  let R := actualEnergyFluxRField F k beta
  let S := actualEnergyFluxSField F k beta
  let phi : (ℂ × ℂ) × ℂ → ℂ := fun p =>
    p.1.1+(4*((k : ℝ)-1)) • p.1.2-(2*((k : ℝ)-1)) • p.2
  have hphi : ContDiffAt ℝ 1 phi ((P z, R z), S z) := by
    dsimp [phi]
    fun_prop
  have hpair := local_lipschitz_prodMk P R z hfields.1 hfields.2.1
  have htriple := local_lipschitz_prodMk (fun w => (P w, R w)) S z
    hpair hfields.2.2
  have h := local_lipschitz_comp (fun w => ((P w, R w), S w)) phi z
    htriple hphi.exists_lipschitzOnWith
  have heq : actualEnergyFluxField F k beta =
      (fun w => phi ((P w, R w), S w)) := by
    ext w
    rfl
  rw [heq]
  exact h

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxField_locally_lipschitz_punctured_disk
