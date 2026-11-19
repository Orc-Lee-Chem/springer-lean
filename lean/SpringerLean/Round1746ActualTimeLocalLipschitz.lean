import SpringerLean.Round1735ActualPFluxDifferentiability
import Mathlib.Analysis.Calculus.ContDiff.RCLike

open Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

theorem actualHarmonic_contDiffAt_real
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ContDiffAt ℝ 1 (actualHarmonic F) z := by
  have hzc : conj z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_conj] using hz
  have hg : ContDiffAt ℝ 1 (exteriorForwardGerm F) (conj z) :=
    (exteriorForwardGerm_analyticOnNhd_unitBall F hc (conj z) hzc).restrictScalars.contDiffAt
  have hconj : ContDiffAt ℝ 1 (fun w : ℂ => conj w) z :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt
  exact contDiffAt_id.add (hg.comp z hconj)

/-- The physical time is C1 throughout the regular source region.
This is used to transfer the globally Lipschitz multiplier splines
to locally Lipschitz physical multiplier compositions at all knots. -/
theorem actualHarmonicMultiplierTime_contDiffAt_regular
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0) :
    ContDiffAt ℝ 1 (actualHarmonicMultiplierTime F k) z := by
  have hr : ContDiffAt ℝ 1 (fun w : ℂ => ‖w‖) z :=
    contDiffAt_id.norm (𝕜 := ℂ) hz0
  have hy : ContDiffAt ℝ 1 (fun w => ‖actualHarmonic F w‖) z :=
    (actualHarmonic_contDiffAt_real F hc hz).norm (𝕜 := ℂ) hH
  have hnum : ContDiffAt ℝ 1 (fun w : ℂ => (k : ℝ)*(1-‖w‖)) z :=
    contDiffAt_const.mul (contDiffAt_const.sub hr)
  change ContDiffAt ℝ 1
    (fun w => ((k : ℝ)*(1-‖w‖)) * (‖actualHarmonic F w‖)⁻¹) z
  exact hnum.mul (hy.inv (norm_ne_zero_iff.mpr hH))

theorem actualHarmonicMultiplierTime_locally_lipschitz_regular
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0) :
    ∃ K : NNReal, ∃ s ∈ 𝓝 z,
      LipschitzOnWith K (actualHarmonicMultiplierTime F k) s :=
  (actualHarmonicMultiplierTime_contDiffAt_regular
    F hc k hz hz0 hH).exists_lipschitzOnWith

/-- The same neighbourhood works for all three physical multiplier
compositions. Their knots do not need to be excluded. -/
theorem actualEnergyMultiplier_compositions_locally_lipschitz_regular
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0) :
    ∃ s ∈ 𝓝 z,
      (∃ K : NNReal, LipschitzOnWith K
        (fun w => energyMultiplierChi (actualHarmonicMultiplierTime F k w)) s) ∧
      (∃ K : NNReal, LipschitzOnWith K
        (fun w => energyMultiplierF (actualHarmonicMultiplierTime F k w)) s) ∧
      (∃ K : NNReal, LipschitzOnWith K
        (fun w => energyMultiplierSigma (actualHarmonicMultiplierTime F k w)) s) := by
  obtain ⟨K, s, hs, ht⟩ := actualHarmonicMultiplierTime_locally_lipschitz_regular
    F hc k hz hz0 hH
  exact ⟨s, hs,
    ⟨_, energyMultiplierChi_lipschitz.comp_lipschitzOnWith ht⟩,
    ⟨_, energyMultiplierF_lipschitz.comp_lipschitzOnWith ht⟩,
    ⟨_, energyMultiplierSigma_lipschitz.comp_lipschitzOnWith ht⟩⟩

end SpringerLean

#print axioms SpringerLean.actualHarmonicMultiplierTime_locally_lipschitz_regular
#print axioms SpringerLean.actualEnergyMultiplier_compositions_locally_lipschitz_regular
