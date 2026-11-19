import SpringerLean.Round1756ActualCutoffFluxLocalLipschitz
import Mathlib.Analysis.Calculus.Rademacher

open MeasureTheory Filter

namespace SpringerLean

theorem actualEnergyFluxField_differentiableAt_disk_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1) :
    ∀ᵐ z ∂(volume : Measure ℂ), ‖z‖ < 1 →
      DifferentiableAt ℝ (actualEnergyFluxField F k beta) z := by
  filter_upwards [actualEnergyMultiplier_compositions_differentiableAt_regular_ae
    F hc k] with z hm hz
  by_cases hH : actualHarmonic F z = 0
  · exact (actualEnergyFluxField_hasFDerivAt_zero_at_filling_zero
      F hc k hk beta hbeta hz hH).differentiableAt
  · have hz0 : z ≠ 0 := by
      intro h
      subst z
      exact hH (by simp [actualHarmonic, exteriorForwardGerm_zero])
    have hreg := (actualMultiplierRegularSet_mem_iff F z).mpr ⟨hz, hH, hz0⟩
    obtain ⟨hchi, hphi, hs⟩ := hm hreg
    have hP := actualEnergyFluxPField_differentiableAt_regular F hc k beta hz hchi
    have hR := actualEnergyFluxRField_differentiableAt_regular F hc k beta hz hz0 hH hphi
    have hS := actualEnergyFluxSField_differentiableAt_regular F hc k beta hz hH hs
    have hd := (hP.add (hR.const_smul (4*((k : ℝ)-1)))).sub
      (hS.const_smul (2*((k : ℝ)-1)))
    convert hd using 1
    ext w
    rfl

/-- The Cartesian product rule for a real scalar cutoff and a plane
field, with the derivative of the cutoff evaluated on that field. -/
theorem actualCartesianDiv_real_smul_product
    (η : ℂ → ℝ) (J : ℂ → ℂ) (z : ℂ)
    (hη : DifferentiableAt ℝ η z) (hJ : DifferentiableAt ℝ J z) :
    actualCartesianDiv (fun w => η w • J w) z =
      η z * actualCartesianDiv J z + (fderiv ℝ η z) (J z) := by
  have hre : DifferentiableAt ℝ (fun w => (J w).re) z :=
    Complex.reCLM.differentiableAt.comp z hJ
  have him : DifferentiableAt ℝ (fun w => (J w).im) z :=
    Complex.imCLM.differentiableAt.comp z hJ
  have heval : (fderiv ℝ η z) (J z) =
      (J z).re*(fderiv ℝ η z) (1 : ℂ) +
        (J z).im*(fderiv ℝ η z) Complex.I := by
    have hdecomp : J z = (J z).re • (1 : ℂ) + (J z).im • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hdecomp]
    simp only [map_add, map_smul, smul_eq_mul]
  simp only [actualCartesianDiv, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  rw [fderiv_fun_mul hη hre, fderiv_fun_mul hη him, heval]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem actualEnergyCutoffFlux_divergence_product_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ z ∂(volume : Measure ℂ), ‖z‖ < 1 →
      actualCartesianDiv (actualEnergyCutoffFlux F k beta ε) z =
        radialEnergyCutoff ε z * actualCartesianDiv (actualEnergyFluxField F k beta) z +
          actualEnergyCutoffError F k beta ε z := by
  filter_upwards [actualEnergyFluxField_differentiableAt_disk_ae F hc k hk beta hbeta,
    (radialEnergyCutoff_lipschitz hε).ae_differentiableAt
      (μ := (volume : Measure ℂ))] with z hJ hη hz
  exact actualCartesianDiv_real_smul_product _ _ z hη (hJ hz)

end SpringerLean

#print axioms SpringerLean.actualEnergyCutoffFlux_divergence_product_ae
