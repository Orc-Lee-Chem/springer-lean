import SpringerLean.Round1760ActualCutoffDivergenceProduct
import SpringerLean.Round1759LipschitzCartesianDivergence
import SpringerLean.Round1743CutoffEnergyLimit

open Filter MeasureTheory Metric
open scoped Topology

namespace SpringerLean.AnalyticRevision

noncomputable section

/-- Cut both collars of the source disk before integrating the divergence. -/
def cutFlux (J : ℂ → ℂ) (ε : ℝ) (z : ℂ) : ℂ :=
  radialEnergyCutoff ε z • J z

private theorem cutFlux_locally_lipschitz
    (J : ℂ → ℂ)
    (hlocal : ∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 →
      ∃ K : NNReal, ∃ s ∈ 𝓝 z, LipschitzOnWith K J s)
    {ε : ℝ} (hε : 0 < ε) :
    LocallyLipschitz (cutFlux J ε) := by
  intro z
  by_cases hz : ‖z‖ < 1 ∧ z ≠ 0
  · have hJ := hlocal z hz.1 hz.2
    have hη : ∃ K : NNReal, ∃ s ∈ 𝓝 z,
        LipschitzOnWith K (radialEnergyCutoff ε) s :=
      ⟨_, Set.univ, Filter.univ_mem,
        lipschitzOnWith_univ.mpr (radialEnergyCutoff_lipschitz hε)⟩
    have hmul : ContDiffAt ℝ 1 (fun p : ℝ × ℂ => p.1 • p.2)
        (radialEnergyCutoff ε z, J z) := by fun_prop
    exact local_lipschitz_comp
      (fun w => (radialEnergyCutoff ε w, J w))
      (fun p : ℝ × ℂ => p.1 • p.2) z
      (local_lipschitz_prodMk _ _ z hη hJ) hmul.exists_lipschitzOnWith
  · have heq : cutFlux J ε =ᶠ[𝓝 z]
        (fun _ : ℂ => (0 : ℂ)) := by
      by_cases hz0 : z = 0
      · have hi : ‖z‖ < ε := by simpa [hz0] using hε
        filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hi)]
          with w hw
        simp [cutFlux, radialEnergyCutoff_eq_zero_inner hε hw.le]
      · have ho : 1-ε < ‖z‖ := by
          have hz1 : 1 ≤ ‖z‖ := le_of_not_gt (fun hz1 => hz ⟨hz1, hz0⟩)
          linarith
        filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds ho)]
          with w hw
        simp [cutFlux, radialEnergyCutoff_eq_zero_outer hε hw.le]
    exact local_lipschitz_of_eventuallyEq _ _ z heq
      (show ContDiffAt ℝ 1 (fun _ : ℂ => (0 : ℂ)) z from
        contDiffAt_const).exists_lipschitzOnWith

private theorem cutFlux_lipschitz
    (J : ℂ → ℂ)
    (hlocal : ∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 →
      ∃ K : NNReal, ∃ s ∈ 𝓝 z, LipschitzOnWith K J s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : NNReal, LipschitzWith K (cutFlux J ε) := by
  let Jε := cutFlux J ε
  have hLL := cutFlux_locally_lipschitz J hlocal hε
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (s := closedBall (0 : ℂ) 2) (isCompact_closedBall (0 : ℂ) 2) hLL.locallyLipschitzOn
  have hzero (w : ℂ) (hw : 1 ≤ ‖w‖) : Jε w = 0 := by
    simp [Jε, cutFlux,
      radialEnergyCutoff_eq_zero_outer hε (by linarith : 1-ε ≤ ‖w‖)]
  have hzero0 : Jε 0 = 0 := by
    simp [Jε, cutFlux,
      radialEnergyCutoff_eq_zero_inner hε (by simpa using hε.le : ‖(0 : ℂ)‖ ≤ ε)]
  have hunit (w : ℂ) (hw : ‖w‖ ≤ 1) : ‖Jε w‖ ≤ (K : ℝ) := by
    have hw2 : w ∈ closedBall (0 : ℂ) 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using (hw.trans (by norm_num))
    have hz2 : (0 : ℂ) ∈ closedBall (0 : ℂ) 2 := by simp
    have h := hK.dist_le_mul w hw2 0 hz2
    change dist (Jε w) (Jε 0) ≤ (K : ℝ)*dist w 0 at h
    rw [hzero0, dist_zero_right, dist_zero_right] at h
    exact h.trans (by nlinarith [K.coe_nonneg])
  have hout (w v : ℂ) (hw : 2 < ‖w‖) :
      dist (Jε w) (Jε v) ≤ (K : ℝ)*dist w v := by
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

def cutFluxError (J : ℂ → ℂ) (ε : ℝ) (z : ℂ) : ℝ :=
  (fderiv ℝ (radialEnergyCutoff ε) z) (J z)

private theorem cutFluxError_measurable (J : ℂ → ℂ)
    (hJ : AEStronglyMeasurable J (volume.restrict (ball (0:ℂ) 1))) (ε : ℝ) :
    AEStronglyMeasurable (cutFluxError J ε) (volume.restrict (ball (0:ℂ) 1)) := by
  have hL := (measurable_fderiv ℝ (radialEnergyCutoff ε)).aemeasurable
    (μ := volume.restrict (ball (0:ℂ) 1))
  have happ : Continuous (fun p : (ℂ →L[ℝ] ℝ) × ℂ => p.1 p.2) := by fun_prop
  exact (happ.measurable.comp_aemeasurable (hL.prodMk hJ.aemeasurable)).aestronglyMeasurable

/-- Local Lipschitz regularity and the collar bound suffice to integrate
the weighted divergence and pass to the open-disk limit. -/
theorem cutFlux_integral_le
    (J : ℂ → ℂ) (P Q M : ℂ → ℝ) (b : ℝ)
    (hlocal : ∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 →
      ∃ K : NNReal, ∃ s ∈ 𝓝 z, LipschitzOnWith K J s)
    (hJm : AEStronglyMeasurable J (volume.restrict (ball (0:ℂ) 1)))
    (hJd : ∀ᵐ z ∂(volume : Measure ℂ), ‖z‖ < 1 → DifferentiableAt ℝ J z)
    (hP : IntegrableOn P (ball (0:ℂ) 1)) (hQ : IntegrableOn Q (ball (0:ℂ) 1))
    (hM : IntegrableOn M (ball (0:ℂ) 1))
    (hM₀ : ∀ z : ℂ, ‖z‖ < 1 → 0 ≤ M z)
    (hbound : ∀ z : ℂ, ‖z‖ < 1 → ‖J z‖ ≤ min ‖z‖ (1-‖z‖) * M z)
    (hpoint : ∀ᵐ z ∂(volume : Measure ℂ), ‖z‖ < 1 →
      P z + b*actualCartesianDiv J z ≤ Q z) :
    (∫ z in ball (0:ℂ) 1, P z ∂volume) ≤ (∫ z in ball (0:ℂ) 1, Q z ∂volume) := by
  let μ : Measure ℂ := volume.restrict (ball (0:ℂ) 1)
  let ε : ℕ → ℝ := fun j => 1/((j:ℝ)+2)
  let η : ℕ → ℂ → ℝ := fun j => radialEnergyCutoff (ε j)
  let B : ℕ → ℝ := fun j => ∫ z, cutFluxError J (ε j) z ∂μ
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2))
  have hmem : ∀ᵐ z ∂μ, ‖z‖ < 1 := by
    simpa only [mem_ball, dist_zero_right] using (ae_restrict_mem isOpen_ball.measurableSet :
      ∀ᵐ z ∂μ, z ∈ ball (0:ℂ) 1)
  have hz₀ : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
    apply ae_iff.mpr
    simp
  have hηlim : ∀ᵐ z ∂μ, Tendsto (fun j => η j z) atTop (𝓝 1) := by
    filter_upwards [ae_restrict_of_ae hz₀,hmem] with z hz₀ hz
    apply tendsto_const_nhds.congr'
    filter_upwards [radialEnergyCutoff_eventually_one ε hε hlim hz₀ hz] with j hj
    exact hj.symm
  have hlocalPoint : ∀ᵐ z ∂μ, P z+b*actualCartesianDiv J z ≤ Q z := by
    filter_upwards [ae_restrict_of_ae hpoint,hmem] with z hp hz
    exact hp hz
  have herrorMeas (j : ℕ) : AEStronglyMeasurable (cutFluxError J (ε j)) μ :=
    cutFluxError_measurable J hJm (ε j)
  have herrorBound (j : ℕ) : ∀ᵐ z ∂μ, ‖cutFluxError J (ε j) z‖ ≤ 4*M z := by
    filter_upwards [hmem] with z hz
    by_cases hcore : 2*ε j < ‖z‖ ∧ ‖z‖ < 1-2*ε j
    · have hzero := radialEnergyCutoff_fderiv_zero_core (hε j) hcore.1 hcore.2
      simp only [cutFluxError,hzero,zero_apply,norm_zero]
      exact mul_nonneg (by norm_num) (hM₀ z hz)
    · have hmin : min ‖z‖ (1-‖z‖) ≤ 2*ε j := by
        by_cases hi : 2*ε j < ‖z‖
        · have ho : 1-2*ε j ≤ ‖z‖ := le_of_not_gt (fun ho => hcore ⟨hi,ho⟩)
          exact (min_le_right _ _).trans (by linarith)
        · exact (min_le_left _ _).trans (le_of_not_gt hi)
      have hMz := hM₀ z hz
      calc
        _ ≤ ‖fderiv ℝ (radialEnergyCutoff (ε j)) z‖*‖J z‖ :=
          (fderiv ℝ (radialEnergyCutoff (ε j)) z).le_opNorm (J z)
        _ ≤ (2/ε j)*(min ‖z‖ (1-‖z‖)*M z) :=
          mul_le_mul (radialEnergyCutoff_fderiv_norm_le (hε j) z)
            (hbound z hz) (norm_nonneg _) (by positivity [hε j])
        _ ≤ (2/ε j)*((2*ε j)*M z) := by gcongr
        _ = _ := by field_simp [ne_of_gt (hε j)]; ring
  have hmajor : Integrable (fun z => 4*M z) μ := hM.const_mul _
  have herrorInt (j : ℕ) : Integrable (cutFluxError J (ε j)) μ :=
    hmajor.mono' (herrorMeas j) (herrorBound j)
  have herrorPt : ∀ᵐ z ∂μ, Tendsto (fun j => cutFluxError J (ε j) z) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_of_ae hz₀,hmem] with z hz₀ hz
    apply tendsto_const_nhds.congr'
    filter_upwards [radialEnergyCutoff_eventually_fderiv_zero ε hε hlim hz₀ hz] with j hj
    simp [cutFluxError,hj]
  have hBlim : Tendsto B atTop (𝓝 0) := by
    simpa only [B,integral_zero] using
      tendsto_integral_of_dominated_convergence _ herrorMeas hmajor herrorBound herrorPt
  have hparts (j : ℕ) :
      Integrable (fun z => η j z*actualCartesianDiv J z) μ ∧
        (∫ z, η j z*actualCartesianDiv J z ∂μ) = -B j := by
    let Jε := cutFlux J (ε j)
    obtain ⟨K,hLip⟩ := cutFlux_lipschitz J hlocal (hε j)
    have hzero (z : ℂ) (hz : 1 ≤ ‖z‖) : Jε z = 0 := by
      simp [Jε, cutFlux, radialEnergyCutoff_eq_zero_outer (hε j) (by linarith [hε j])]
    obtain ⟨hInt,hInt₀⟩ := integral_actualCartesianDiv_zero_of_lipschitz_unit_support Jε K hLip hzero
    have hout (z : ℂ) (hz : z ∉ ball (0:ℂ) 1) : actualCartesianDiv Jε z = 0 := by
      have hz₁ : 1 ≤ ‖z‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hz
      have hlt : 1-ε j < ‖z‖ := by linarith [hε j]
      have heq : Jε =ᶠ[𝓝 z] (fun _ : ℂ => (0:ℂ)) := by
        filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hlt)] with w hw
        simp [Jε,cutFlux,radialEnergyCutoff_eq_zero_outer (hε j) hw.le]
      have hre : (fun w => (Jε w).re) =ᶠ[𝓝 z] (fun _ : ℂ => (0:ℝ)) :=
        heq.mono (fun w hw => by simp [hw])
      have him : (fun w => (Jε w).im) =ᶠ[𝓝 z] (fun _ : ℂ => (0:ℝ)) :=
        heq.mono (fun w hw => by simp [hw])
      have hr : fderiv ℝ (fun w => (Jε w).re) z = 0 := by simpa using hre.fderiv_eq (𝕜 := ℝ)
      have hi : fderiv ℝ (fun w => (Jε w).im) z = 0 := by simpa using him.fderiv_eq (𝕜 := ℝ)
      simp [actualCartesianDiv,hr,hi]
    have hprod : (fun z => η j z*actualCartesianDiv J z) =ᵐ[μ]
        (fun z => actualCartesianDiv Jε z-cutFluxError J (ε j) z) := by
      filter_upwards [ae_restrict_of_ae hJd,hmem,ae_restrict_of_ae
        ((radialEnergyCutoff_lipschitz (hε j)).ae_differentiableAt
          (μ := (volume : Measure ℂ)))] with z hd hz hηd
      have hp := actualCartesianDiv_real_smul_product (radialEnergyCutoff (ε j)) J z hηd (hd hz)
      change _ = actualCartesianDiv (fun w => radialEnergyCutoff (ε j) w • J w) z - _
      rw [hp]
      simp [η,cutFluxError]
    have hIntDisk : Integrable (actualCartesianDiv Jε) μ := hInt.integrableOn
    have hIntDisk₀ : (∫ z, actualCartesianDiv Jε z ∂μ) = 0 :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hout).trans hInt₀
    refine ⟨(hIntDisk.sub (herrorInt j)).congr hprod.symm,?_⟩
    rw [integral_congr_ae hprod,integral_sub hIntDisk (herrorInt j),hIntDisk₀,zero_sub]
  exact integral_energy_le_of_cutoff_flux_balance μ P Q (actualCartesianDiv J) b η B
    hP hQ (fun _ => radialEnergyCutoff_continuous.aestronglyMeasurable)
    (fun j => Filter.Eventually.of_forall (radialEnergyCutoff_bounds (ε j)))
    hηlim hlocalPoint (fun j => (hparts j).1) (fun j => (hparts j).2) hBlim

end
end SpringerLean.AnalyticRevision
