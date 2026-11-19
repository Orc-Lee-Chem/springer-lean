import SpringerLean.Round1755ActualCombinedFluxLocalLipschitz
import SpringerLean.Round1745ActualCollarErrorLimit

open Filter Metric
open scoped Topology

namespace SpringerLean

noncomputable def actualEnergyCutoffFlux
    (F : ℂ → ℂ) (k : ℕ) (beta : ℂ) (ε : ℝ) (z : ℂ) : ℂ :=
  radialEnergyCutoff ε z • actualEnergyFluxField F k beta z

/-- The compactly cut physical flux is locally Lipschitz globally,
even though no boundary extension of the original map is assumed. -/
theorem actualEnergyCutoffFlux_locally_lipschitz
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    LocallyLipschitz (actualEnergyCutoffFlux F k beta ε) := by
  intro z
  by_cases hz : ‖z‖ < 1 ∧ z ≠ 0
  · have hJ := actualEnergyFluxField_locally_lipschitz_punctured_disk
      F hc k hk beta hbeta hz.1 hz.2
    have hη : ∃ K : NNReal, ∃ s ∈ 𝓝 z,
        LipschitzOnWith K (radialEnergyCutoff ε) s :=
      ⟨_, Set.univ, Filter.univ_mem,
        lipschitzOnWith_univ.mpr (radialEnergyCutoff_lipschitz hε)⟩
    have hmul : ContDiffAt ℝ 1 (fun p : ℝ × ℂ => p.1 • p.2)
        (radialEnergyCutoff ε z, actualEnergyFluxField F k beta z) := by fun_prop
    exact local_lipschitz_comp
      (fun w => (radialEnergyCutoff ε w, actualEnergyFluxField F k beta w))
      (fun p : ℝ × ℂ => p.1 • p.2) z
      (local_lipschitz_prodMk _ _ z hη hJ) hmul.exists_lipschitzOnWith
  · have heq : actualEnergyCutoffFlux F k beta ε =ᶠ[𝓝 z]
        (fun _ : ℂ => (0 : ℂ)) := by
      by_cases hz0 : z = 0
      · have hi : ‖z‖ < ε := by simpa [hz0] using hε
        filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hi)]
          with w hw
        simp [actualEnergyCutoffFlux, radialEnergyCutoff_eq_zero_inner hε hw.le]
      · have ho : 1-ε < ‖z‖ := by
          have hz1 : 1 ≤ ‖z‖ := le_of_not_gt (fun hz1 => hz ⟨hz1, hz0⟩)
          linarith
        filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds ho)]
          with w hw
        simp [actualEnergyCutoffFlux, radialEnergyCutoff_eq_zero_outer hε hw.le]
    exact local_lipschitz_of_eventuallyEq _ _ z heq
      (show ContDiffAt ℝ 1 (fun _ : ℂ => (0 : ℂ)) z from
        contDiffAt_const).exists_lipschitzOnWith

theorem actualEnergyCutoffFlux_hasCompactSupport
    (F : ℂ → ℂ) (k : ℕ) (beta : ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (actualEnergyCutoffFlux F k beta ε) := by
  have hsub : Function.support (actualEnergyCutoffFlux F k beta ε) ⊆
      closedBall (0 : ℂ) (1-ε) := by
    intro z hz
    have hnorm : ‖z‖ ≤ 1-ε := by
      by_contra h
      have hz0 : actualEnergyCutoffFlux F k beta ε z = 0 := by
        simp [actualEnergyCutoffFlux, radialEnergyCutoff_eq_zero_outer hε
          (le_of_lt (lt_of_not_ge h))]
      exact hz hz0
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
  exact (isCompact_closedBall (0 : ℂ) (1-ε)).of_isClosed_subset isClosed_closure
    (closure_minimal hsub isClosed_closedBall)

/-- A single global Lipschitz constant exists for each fixed physical
cutoff. Compactness is used only after both source boundaries have
been removed. -/
theorem actualEnergyCutoffFlux_lipschitz
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ K : NNReal, LipschitzWith K (actualEnergyCutoffFlux F k beta ε) := by
  let J := actualEnergyCutoffFlux F k beta ε
  have hLL := actualEnergyCutoffFlux_locally_lipschitz F hc k hk beta hbeta hε hε1
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (s := closedBall (0 : ℂ) 2) (isCompact_closedBall (0 : ℂ) 2) hLL.locallyLipschitzOn
  have hzero (w : ℂ) (hw : 1 ≤ ‖w‖) : J w = 0 := by
    simp [J, actualEnergyCutoffFlux,
      radialEnergyCutoff_eq_zero_outer hε (by linarith : 1-ε ≤ ‖w‖)]
  have hzero0 : J 0 = 0 := by
    simp [J, actualEnergyCutoffFlux,
      radialEnergyCutoff_eq_zero_inner hε (by simpa using hε.le : ‖(0 : ℂ)‖ ≤ ε)]
  have hunit (w : ℂ) (hw : ‖w‖ ≤ 1) : ‖J w‖ ≤ (K : ℝ) := by
    have hw2 : w ∈ closedBall (0 : ℂ) 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using (hw.trans (by norm_num))
    have hz2 : (0 : ℂ) ∈ closedBall (0 : ℂ) 2 := by simp
    have h := hK.dist_le_mul w hw2 0 hz2
    change dist (J w) (J 0) ≤ (K : ℝ)*dist w 0 at h
    rw [hzero0, dist_zero_right, dist_zero_right] at h
    exact h.trans (by nlinarith [K.coe_nonneg])
  have hout (w v : ℂ) (hw : 2 < ‖w‖) :
      dist (J w) (J v) ≤ (K : ℝ)*dist w v := by
    have hzw := hzero w (by linarith)
    by_cases hv : ‖v‖ ≤ 1
    · have hdist : 1 ≤ dist w v := by
        rw [dist_eq_norm]
        have hn := norm_sub_norm_le w v
        linarith
      rw [hzw, dist_zero_left]
      exact (hunit v hv).trans (by nlinarith [K.coe_nonneg])
    · rw [hzw, hzero v (le_of_not_ge hv), dist_self]
      positivity
  refine ⟨K, LipschitzWith.of_dist_le_mul ?_⟩
  intro w v
  by_cases hw : ‖w‖ ≤ 2
  · by_cases hv : ‖v‖ ≤ 2
    · exact hK.dist_le_mul w (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw)
        v (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv)
    · simpa only [dist_comm] using hout v w (lt_of_not_ge hv)
  · exact hout w v (lt_of_not_ge hw)

end SpringerLean

#print axioms SpringerLean.actualEnergyCutoffFlux_locally_lipschitz
#print axioms SpringerLean.actualEnergyCutoffFlux_hasCompactSupport
#print axioms SpringerLean.actualEnergyCutoffFlux_lipschitz
