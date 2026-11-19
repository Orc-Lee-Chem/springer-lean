import SpringerLean.Round1748VanishingSquareQuotientLipschitz
import SpringerLean.Round1746ActualTimeLocalLipschitz

open Filter Metric
open scoped Topology ComplexConjugate

namespace SpringerLean

theorem actualHarmonicPhaseField_contDiffAt_real
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ContDiffAt ℝ 1 (actualHarmonicPhaseField F k beta) z := by
  have hpower : ContDiffAt ℝ 1
      (fun w => beta*(actualHarmonic F w)^k) z :=
    contDiffAt_const.mul ((actualHarmonic_contDiffAt_real F hc hz).pow k)
  exact Complex.imCLM.contDiff.contDiffAt.comp z hpower

/-- The two quotient amplitudes of the R and S fluxes are locally
Lipschitz at EVERY interior filling point, including its entire zero
set. They use the same zero-divisor extension as the actual fields. -/
theorem actualEnergyFlux_quotient_amplitudes_locally_lipschitz
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 1 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ s ∈ 𝓝 z,
      (∃ K : NNReal, LipschitzOnWith K
        (fun w => (actualHarmonicPhaseField F k beta w)^2 /
          ‖actualHarmonic F w‖) s) ∧
      (∃ K : NNReal, LipschitzOnWith K
        (fun w => ((actualHarmonicPhaseField F k beta w : ℂ)^2) /
          conj (actualHarmonic F w)) s) := by
  let U := actualHarmonicPhaseField F k beta
  let Uc : ℂ → ℂ := fun w => (U w : ℂ)
  have hUc : ContDiffAt ℝ 1 Uc z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z
      (actualHarmonicPhaseField_contDiffAt_real F hc k beta hz)
  obtain ⟨Ku, su, hsu, hUlip⟩ := hUc.exists_lipschitzOnWith
  obtain ⟨Kh, sh, hsh, hHlip⟩ :=
    (actualHarmonic_contDiffAt_real F hc hz).exists_lipschitzOnWith
  let s : Set ℂ := su ∩ sh ∩ ball (0 : ℂ) 1
  have hs : s ∈ 𝓝 z := inter_mem (inter_mem hsu hsh)
    (Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball, dist_zero_right] using hz))
  have hUlip' : LipschitzOnWith Ku Uc s :=
    hUlip.mono (fun _ h => h.1.1)
  have hHlip' : LipschitzOnWith Kh (actualHarmonic F) s :=
    hHlip.mono (fun _ h => h.1.2)
  let C : NNReal := ⟨(2 : ℝ)^(k-1), by positivity⟩
  have hvanish : ∀ w ∈ s, ‖Uc w‖ ≤ (C : ℝ)*‖actualHarmonic F w‖ := by
    intro w hw
    have hw' : ‖w‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hw.2
    have hU := actualHarmonicPhaseField_abs_le_power F k beta w hbeta
    have hy := actualHarmonic_norm_le_two_norm F hc hw'
    have hy2 : ‖actualHarmonic F w‖ ≤ 2 := by linarith
    have hp := pow_le_pow_left₀ (norm_nonneg _) hy2 (k-1)
    have hpow : ‖actualHarmonic F w‖^k =
        ‖actualHarmonic F w‖^(k-1)*‖actualHarmonic F w‖ := by
      rw [← pow_succ]
      congr 1
      omega
    have hn : ‖Uc w‖ = |U w| := by simp [Uc]
    rw [hn]
    calc
      _ ≤ _ := hU
      _ = _ := hpow
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
  have hnormLip := lipschitzWith_one_norm.comp_lipschitzOnWith hHlip'
  have hVrealLip := Complex.ofRealCLM.lipschitz.comp_lipschitzOnWith hnormLip
  have hVconjLip := Complex.conjCLE.toContinuousLinearMap.lipschitz.comp_lipschitzOnWith hHlip'
  have hVr : ∀ w ∈ s, ‖Uc w‖ ≤ (C : ℝ)*‖(‖actualHarmonic F w‖ : ℂ)‖ := by
    intro w hw
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using hvanish w hw
  have hVc : ∀ w ∈ s, ‖Uc w‖ ≤ (C : ℝ)*‖conj (actualHarmonic F w)‖ := by
    intro w hw
    simpa only [Complex.norm_conj] using hvanish w hw
  have hR := lipschitzOnWith_vanishing_square_quotient Uc
    (fun w => (‖actualHarmonic F w‖ : ℂ)) s _ _ C hUlip' hVrealLip hVr
  have hS := lipschitzOnWith_vanishing_square_quotient Uc
    (fun w => conj (actualHarmonic F w)) s _ _ C hUlip' hVconjLip hVc
  have hre := Complex.reCLM.lipschitz.comp_lipschitzOnWith hR
  refine ⟨s, hs, ⟨‖Complex.reCLM‖₊ *
    (2*C*Ku+C^2*(‖Complex.ofRealCLM‖₊*(1*Kh))), ?_⟩, ⟨_, hS⟩⟩
  convert hre using 1
  ext w
  simp [Uc, U, ← Complex.ofReal_pow, ← Complex.ofReal_div]

end SpringerLean

#print axioms SpringerLean.actualEnergyFlux_quotient_amplitudes_locally_lipschitz
