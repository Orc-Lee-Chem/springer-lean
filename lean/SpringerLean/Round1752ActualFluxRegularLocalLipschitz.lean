import SpringerLean.Round1749ActualFluxAmplitudesLocalLipschitz
import SpringerLean.Round1750LocalLipschitzOperations
import SpringerLean.Round1751ActualPhaseGradientC1

open Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

/-- All three actual physical flux fields are locally Lipschitz on
the regular source region, without excluding multiplier knots. -/
theorem actualEnergyFluxFields_locally_lipschitz_regular
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 1 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0) :
    (∃ K : NNReal, ∃ s ∈ 𝓝 z,
      LipschitzOnWith K (actualEnergyFluxPField F k beta) s) ∧
    (∃ K : NNReal, ∃ s ∈ 𝓝 z,
      LipschitzOnWith K (actualEnergyFluxRField F k beta) s) ∧
    (∃ K : NNReal, ∃ s ∈ 𝓝 z,
      LipschitzOnWith K (actualEnergyFluxSField F k beta) s) := by
  let U := actualHarmonicPhaseField F k beta
  let t := actualHarmonicMultiplierTime F k
  let chi : ℂ → ℝ := fun w => energyMultiplierChi (t w)
  let phi : ℂ → ℝ := fun w => energyMultiplierF (t w)
  let sigma : ℂ → ℝ := fun w => energyMultiplierSigma (t w)
  let Ar : ℂ → ℝ := fun w => (U w)^2/‖actualHarmonic F w‖
  let As : ℂ → ℂ := fun w => (U w : ℂ)^2/conj (actualHarmonic F w)
  let Lr (f : ℂ → ℝ) := ∃ K : NNReal, ∃ s ∈ 𝓝 z, LipschitzOnWith K f s
  let Lc (f : ℂ → ℂ) := ∃ K : NNReal, ∃ s ∈ 𝓝 z, LipschitzOnWith K f s
  obtain ⟨sm, hsm, ⟨Kchi, hchi⟩, ⟨Kphi, hphi⟩, ⟨Ks, hs⟩⟩ :=
    actualEnergyMultiplier_compositions_locally_lipschitz_regular
      F hc k hz hz0 hH
  have hchi' : Lr chi := ⟨Kchi, sm, hsm, hchi⟩
  have hphi' : Lr phi := ⟨Kphi, sm, hsm, hphi⟩
  have hs' : Lr sigma := ⟨Ks, sm, hsm, hs⟩
  have hU : Lr U :=
    (actualHarmonicPhaseField_contDiffAt_real F hc k beta hz).exists_lipschitzOnWith
  obtain ⟨hUx, hUy⟩ := actualHarmonicPhase_gradient_coordinates_contDiffAt
    F hc k beta hz
  have hP₁ : Lr (fun w => chi w*U w*(fderiv ℝ U w) (1 : ℂ)) :=
    local_lipschitz_mul _ _ z (local_lipschitz_mul _ _ z hchi' hU)
      hUx.exists_lipschitzOnWith
  have hP₂ : Lr (fun w => chi w*U w*(fderiv ℝ U w) Complex.I) :=
    local_lipschitz_mul _ _ z (local_lipschitz_mul _ _ z hchi' hU)
      hUy.exists_lipschitzOnWith
  have hP : Lc (actualEnergyFluxPField F k beta) :=
    local_lipschitz_complex_mk _ _ z hP₁ hP₂
  obtain ⟨sa, hsa, ⟨Kr, hr⟩, ⟨Kas, has⟩⟩ :=
    actualEnergyFlux_quotient_amplitudes_locally_lipschitz F hc k hk beta hbeta hz
  have hAr : Lr Ar := ⟨Kr, sa, hsa, hr⟩
  have hAs : Lc As := ⟨Kas, sa, hsa, has⟩
  have hnorm : ContDiffAt ℝ 1 (fun w : ℂ => ‖w‖) z :=
    contDiffAt_id.norm (𝕜 := ℂ) hz0
  have hninv := hnorm.inv (norm_ne_zero_iff.mpr hz0)
  have hxr : ContDiffAt ℝ 1 (fun w : ℂ => w.re/‖w‖) z := by
    change ContDiffAt ℝ 1 (fun w : ℂ => w.re*(‖w‖)⁻¹) z
    exact Complex.reCLM.contDiff.contDiffAt.mul hninv
  have hyr : ContDiffAt ℝ 1 (fun w : ℂ => w.im/‖w‖) z := by
    change ContDiffAt ℝ 1 (fun w : ℂ => w.im*(‖w‖)⁻¹) z
    exact Complex.imCLM.contDiff.contDiffAt.mul hninv
  have hR₁ := local_lipschitz_mul (fun w => phi w*Ar w)
    (fun w => w.re/‖w‖) z (local_lipschitz_mul _ _ z hphi' hAr)
      hxr.exists_lipschitzOnWith
  have hR₂ := local_lipschitz_mul (fun w => phi w*Ar w)
    (fun w => w.im/‖w‖) z (local_lipschitz_mul _ _ z hphi' hAr)
      hyr.exists_lipschitzOnWith
  have hR : Lc (actualEnergyFluxRField F k beta) := by
    have h := local_lipschitz_complex_mk _ _ z hR₁ hR₂
    convert h using 1
    ext w
    apply Complex.ext <;>
      simp [actualEnergyFluxRField, Ar, U, phi, t, div_eq_mul_inv] <;> ring
  have hAre : Lr (fun w => (As w).re) := local_lipschitz_comp As Complex.re z hAs
    Complex.reCLM.contDiff.contDiffAt.exists_lipschitzOnWith
  have hAim : Lr (fun w => (As w).im) := local_lipschitz_comp As Complex.im z hAs
    Complex.imCLM.contDiff.contDiffAt.exists_lipschitzOnWith
  have hS : Lc (actualEnergyFluxSField F k beta) := by
    have h := local_lipschitz_complex_mk _ _ z
      (local_lipschitz_mul sigma (fun w => (As w).re) z hs' hAre)
      (local_lipschitz_mul sigma (fun w => (As w).im) z hs' hAim)
    convert h using 1
    ext w
    apply Complex.ext <;>
      simp [actualEnergyFluxSField, As, U, sigma, t, div_eq_mul_inv,
        ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im] <;> ring
  exact ⟨hP, hR, hS⟩

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxFields_locally_lipschitz_regular
