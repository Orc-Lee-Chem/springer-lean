import SpringerLean.Round1734ActualMultiplierDifferentiabilityAE

open MeasureTheory

namespace SpringerLean

/-- A real-differentiable pair of coordinates forms a
real-differentiable complex field. -/
theorem complex_mk_differentiableAt_of_coordinates
    (f g : ℂ → ℝ) (z : ℂ)
    (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    DifferentiableAt ℝ (fun w => Complex.mk (f w) (g w)) z := by
  have hpair : DifferentiableAt ℝ (fun w => (f w, g w)) z :=
    hf.prodMk hg
  have h := Complex.equivRealProdCLM.symm.differentiableAt.comp z hpair
  convert h using 1
  ext w
  apply Complex.ext <;>
    simp [Complex.equivRealProdCLM_symm_apply]

/-- The P part of the actual signed flux is differentiable at a
regular point whenever its physical chi multiplier is. -/
theorem actualEnergyFluxPField_differentiableAt_regular
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    (hchi : DifferentiableAt ℝ
      (fun w => energyMultiplierChi
        (actualHarmonicMultiplierTime F k w)) z) :
    DifferentiableAt ℝ (actualEnergyFluxPField F k beta) z := by
  let U := actualHarmonicPhaseField F k beta
  let chi : ℂ → ℝ := fun w =>
    energyMultiplierChi (actualHarmonicMultiplierTime F k w)
  have hU : DifferentiableAt ℝ U z :=
    (actualHarmonicPhaseField_hasFDerivAt F hc k beta hz).differentiableAt
  obtain ⟨hUx, hUy⟩ :=
    actualHarmonicPhase_gradient_coordinates_differentiableAt
      F hc k beta hz
  have hx : DifferentiableAt ℝ
      (fun w => chi w * U w * (fderiv ℝ U w) (1 : ℂ)) z :=
    (hchi.mul hU).mul hUx
  have hy : DifferentiableAt ℝ
      (fun w => chi w * U w * (fderiv ℝ U w) Complex.I) z :=
    (hchi.mul hU).mul hUy
  exact complex_mk_differentiableAt_of_coordinates _ _ z hx hy

end SpringerLean

#print axioms SpringerLean.complex_mk_differentiableAt_of_coordinates
#print axioms SpringerLean.actualEnergyFluxPField_differentiableAt_regular
