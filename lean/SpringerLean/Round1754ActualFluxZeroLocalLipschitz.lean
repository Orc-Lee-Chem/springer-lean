import SpringerLean.Round1752ActualFluxRegularLocalLipschitz
import SpringerLean.Round1753ActualFluxConstantTailNearZero

open Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

/-- At a noncentral filling zero the same physical fluxes are locally
Lipschitz: constant multiplier tails multiply the removable quotient
amplitudes. No isolated-zero hypothesis is used. -/
theorem actualEnergyFluxFields_locally_lipschitz_at_filling_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z = 0) :
    (∃ K : NNReal, ∃ s ∈ 𝓝 z,
      LipschitzOnWith K (actualEnergyFluxPField F k beta) s) ∧
    (∃ K : NNReal, ∃ s ∈ 𝓝 z,
      LipschitzOnWith K (actualEnergyFluxRField F k beta) s) ∧
    (∃ K : NNReal, ∃ s ∈ 𝓝 z,
      LipschitzOnWith K (actualEnergyFluxSField F k beta) s) := by
  let U := actualHarmonicPhaseField F k beta
  let Ar : ℂ → ℝ := fun w => (U w)^2/‖actualHarmonic F w‖
  let As : ℂ → ℂ := fun w => (U w : ℂ)^2/conj (actualHarmonic F w)
  let Lr (f : ℂ → ℝ) := ∃ K : NNReal, ∃ s ∈ 𝓝 z, LipschitzOnWith K f s
  let Lc (f : ℂ → ℂ) := ∃ K : NNReal, ∃ s ∈ 𝓝 z, LipschitzOnWith K f s
  obtain ⟨a, b, c, htail⟩ := actualEnergyFluxFields_constant_tail_near_filling_zero
    F hc k hk beta hz hz0 hH
  let Pt : ℂ → ℂ := fun w =>
    Complex.mk (a*U w*(fderiv ℝ U w) (1 : ℂ))
      (a*U w*(fderiv ℝ U w) Complex.I)
  let Rt : ℂ → ℂ := fun w =>
    Complex.mk ((b*(U w)^2/‖actualHarmonic F w‖)*w.re/‖w‖)
      ((b*(U w)^2/‖actualHarmonic F w‖)*w.im/‖w‖)
  let St : ℂ → ℂ := fun w =>
    Complex.mk (c*(U w)^2*((conj (actualHarmonic F w))⁻¹).re)
      (c*(U w)^2*((conj (actualHarmonic F w))⁻¹).im)
  have hU := actualHarmonicPhaseField_contDiffAt_real F hc k beta hz
  obtain ⟨hUx, hUy⟩ := actualHarmonicPhase_gradient_coordinates_contDiffAt
    F hc k beta hz
  have hPt : Lc Pt :=
    (contDiffAt_complex_mk _ _ z
      ((contDiffAt_const.mul hU).mul hUx)
      ((contDiffAt_const.mul hU).mul hUy)).exists_lipschitzOnWith
  obtain ⟨sa, hsa, ⟨Kr, hr⟩, ⟨Ks, hs⟩⟩ :=
    actualEnergyFlux_quotient_amplitudes_locally_lipschitz F hc k (by omega)
      beta hbeta hz
  have hAr : Lr Ar := ⟨Kr, sa, hsa, hr⟩
  have hAs : Lc As := ⟨Ks, sa, hsa, hs⟩
  have hconst (a : ℝ) : Lr (fun _ : ℂ => a) :=
    (show ContDiffAt ℝ 1 (fun _ : ℂ => a) z from contDiffAt_const).exists_lipschitzOnWith
  have hnorm : ContDiffAt ℝ 1 (fun w : ℂ => ‖w‖) z :=
    contDiffAt_id.norm (𝕜 := ℂ) hz0
  have hninv := hnorm.inv (norm_ne_zero_iff.mpr hz0)
  have hxr : ContDiffAt ℝ 1 (fun w : ℂ => w.re/‖w‖) z := by
    change ContDiffAt ℝ 1 (fun w : ℂ => w.re*(‖w‖)⁻¹) z
    exact Complex.reCLM.contDiff.contDiffAt.mul hninv
  have hyr : ContDiffAt ℝ 1 (fun w : ℂ => w.im/‖w‖) z := by
    change ContDiffAt ℝ 1 (fun w : ℂ => w.im*(‖w‖)⁻¹) z
    exact Complex.imCLM.contDiff.contDiffAt.mul hninv
  have hB : Lr (fun w => b*Ar w) :=
    local_lipschitz_mul _ _ z (hconst b) hAr
  have hRt : Lc Rt := by
    have h := local_lipschitz_complex_mk _ _ z
      (local_lipschitz_mul _ _ z hB hxr.exists_lipschitzOnWith)
      (local_lipschitz_mul _ _ z hB hyr.exists_lipschitzOnWith)
    convert h using 1
    ext w
    apply Complex.ext <;> simp [Rt, Ar, div_eq_mul_inv] <;> ring
  have hAre : Lr (fun w => (As w).re) := local_lipschitz_comp As Complex.re z hAs
    Complex.reCLM.contDiff.contDiffAt.exists_lipschitzOnWith
  have hAim : Lr (fun w => (As w).im) := local_lipschitz_comp As Complex.im z hAs
    Complex.imCLM.contDiff.contDiffAt.exists_lipschitzOnWith
  have hSt : Lc St := by
    have h := local_lipschitz_complex_mk _ _ z
      (local_lipschitz_mul _ _ z (hconst c) hAre)
      (local_lipschitz_mul _ _ z (hconst c) hAim)
    convert h using 1
    ext w
    apply Complex.ext <;>
      simp [St, As, div_eq_mul_inv, ← Complex.ofReal_pow,
        Complex.mul_re, Complex.mul_im] <;> ring
  have hPe : actualEnergyFluxPField F k beta =ᶠ[𝓝 z] Pt :=
    htail.mono (fun _ h => h.1)
  have hRe : actualEnergyFluxRField F k beta =ᶠ[𝓝 z] Rt :=
    htail.mono (fun _ h => h.2.1)
  have hSe : actualEnergyFluxSField F k beta =ᶠ[𝓝 z] St :=
    htail.mono (fun _ h => h.2.2)
  exact ⟨local_lipschitz_of_eventuallyEq _ _ z hPe hPt,
    local_lipschitz_of_eventuallyEq _ _ z hRe hRt,
    local_lipschitz_of_eventuallyEq _ _ z hSe hSt⟩

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxFields_locally_lipschitz_at_filling_zero
