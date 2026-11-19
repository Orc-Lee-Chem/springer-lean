import SpringerLean.Round1732ActualFluxDivergenceAtZero

namespace SpringerLean

/-- Cartesian divergence is additive at points where both fields are
real differentiable. This is the linearity needed to identify the
divergence of the signed combined flux with the earlier P/R/S ledger. -/
theorem actualCartesianDiv_add
    (J K : ℂ → ℂ) (z : ℂ)
    (hJ : DifferentiableAt ℝ J z)
    (hK : DifferentiableAt ℝ K z) :
    actualCartesianDiv (fun w => J w + K w) z =
      actualCartesianDiv J z + actualCartesianDiv K z := by
  have hJre : DifferentiableAt ℝ (fun w => (J w).re) z :=
    Complex.reCLM.differentiableAt.comp z hJ
  have hKre : DifferentiableAt ℝ (fun w => (K w).re) z :=
    Complex.reCLM.differentiableAt.comp z hK
  have hJim : DifferentiableAt ℝ (fun w => (J w).im) z :=
    Complex.imCLM.differentiableAt.comp z hJ
  have hKim : DifferentiableAt ℝ (fun w => (K w).im) z :=
    Complex.imCLM.differentiableAt.comp z hK
  have hre : fderiv ℝ (fun w => (J w).re + (K w).re) z =
      fderiv ℝ (fun w => (J w).re) z +
        fderiv ℝ (fun w => (K w).re) z := by
    have heq : (fun w => (J w).re + (K w).re) =
        (fun w => (J w).re) + (fun w => (K w).re) := by
      ext w
      rfl
    rw [heq]
    exact fderiv_add hJre hKre
  have him : fderiv ℝ (fun w => (J w).im + (K w).im) z =
      fderiv ℝ (fun w => (J w).im) z +
        fderiv ℝ (fun w => (K w).im) z := by
    have heq : (fun w => (J w).im + (K w).im) =
        (fun w => (J w).im) + (fun w => (K w).im) := by
      ext w
      rfl
    rw [heq]
    exact fderiv_add hJim hKim
  simp only [actualCartesianDiv, Complex.add_re, Complex.add_im]
  rw [hre, him]
  simp only [add_apply]
  ring

theorem actualCartesianDiv_real_smul
    (a : ℝ) (J : ℂ → ℂ) (z : ℂ)
    (hJ : DifferentiableAt ℝ J z) :
    actualCartesianDiv (fun w => a • J w) z =
      a * actualCartesianDiv J z := by
  have hJre : DifferentiableAt ℝ (fun w => (J w).re) z :=
    Complex.reCLM.differentiableAt.comp z hJ
  have hJim : DifferentiableAt ℝ (fun w => (J w).im) z :=
    Complex.imCLM.differentiableAt.comp z hJ
  have hre : fderiv ℝ (fun w => (a • J w).re) z =
      a • fderiv ℝ (fun w => (J w).re) z := by
    have heq : (fun w => (a • J w).re) =
        a • (fun w => (J w).re) := by
      ext w
      simp [smul_eq_mul]
    rw [heq]
    exact fderiv_const_smul hJre a
  have him : fderiv ℝ (fun w => (a • J w).im) z =
      a • fderiv ℝ (fun w => (J w).im) z := by
    have heq : (fun w => (a • J w).im) =
        a • (fun w => (J w).im) := by
      ext w
      simp [smul_eq_mul]
    rw [heq]
    exact fderiv_const_smul hJim a
  simp only [actualCartesianDiv, hre, him, smul_apply, smul_eq_mul]
  ring

theorem actualCartesianDiv_sub
    (J K : ℂ → ℂ) (z : ℂ)
    (hJ : DifferentiableAt ℝ J z)
    (hK : DifferentiableAt ℝ K z) :
    actualCartesianDiv (fun w => J w - K w) z =
      actualCartesianDiv J z - actualCartesianDiv K z := by
  have hJre : DifferentiableAt ℝ (fun w => (J w).re) z :=
    Complex.reCLM.differentiableAt.comp z hJ
  have hKre : DifferentiableAt ℝ (fun w => (K w).re) z :=
    Complex.reCLM.differentiableAt.comp z hK
  have hJim : DifferentiableAt ℝ (fun w => (J w).im) z :=
    Complex.imCLM.differentiableAt.comp z hJ
  have hKim : DifferentiableAt ℝ (fun w => (K w).im) z :=
    Complex.imCLM.differentiableAt.comp z hK
  have hre : fderiv ℝ (fun w => (J w).re - (K w).re) z =
      fderiv ℝ (fun w => (J w).re) z -
        fderiv ℝ (fun w => (K w).re) z := by
    have heq : (fun w => (J w).re - (K w).re) =
        (fun w => (J w).re) - (fun w => (K w).re) := by
      ext w
      rfl
    rw [heq]
    exact fderiv_sub hJre hKre
  have him : fderiv ℝ (fun w => (J w).im - (K w).im) z =
      fderiv ℝ (fun w => (J w).im) z -
        fderiv ℝ (fun w => (K w).im) z := by
    have heq : (fun w => (J w).im - (K w).im) =
        (fun w => (J w).im) - (fun w => (K w).im) := by
      ext w
      rfl
    rw [heq]
    exact fderiv_sub hJim hKim
  simp only [actualCartesianDiv, Complex.sub_re, Complex.sub_im, hre, him,
    sub_apply]
  ring

/-- At any point where all three physical fluxes are differentiable,
the divergence of their signed combination is exactly the earlier
P/R/S divergence ledger. -/
theorem actualCartesianDiv_actualEnergyFluxField_eq
    (F : ℂ → ℂ) (k : ℕ) (beta z : ℂ)
    (hP : DifferentiableAt ℝ (actualEnergyFluxPField F k beta) z)
    (hR : DifferentiableAt ℝ (actualEnergyFluxRField F k beta) z)
    (hS : DifferentiableAt ℝ (actualEnergyFluxSField F k beta) z) :
    actualCartesianDiv (actualEnergyFluxField F k beta) z =
      actualEnergyFluxDiv F k beta z := by
  let a : ℝ := 4 * ((k : ℝ) - 1)
  let b : ℝ := 2 * ((k : ℝ) - 1)
  have hRa : DifferentiableAt ℝ
      (fun w => a • actualEnergyFluxRField F k beta w) z := hR.const_smul a
  have hSb : DifferentiableAt ℝ
      (fun w => b • actualEnergyFluxSField F k beta w) z := hS.const_smul b
  have hPR : DifferentiableAt ℝ
      (fun w => actualEnergyFluxPField F k beta w +
        a • actualEnergyFluxRField F k beta w) z := hP.add hRa
  change actualCartesianDiv
      (fun w => (actualEnergyFluxPField F k beta w +
        a • actualEnergyFluxRField F k beta w) -
        b • actualEnergyFluxSField F k beta w) z = _
  rw [actualCartesianDiv_sub _ _ _ hPR hSb,
    actualCartesianDiv_add _ _ _ hP hRa,
    actualCartesianDiv_real_smul _ _ _ hR,
    actualCartesianDiv_real_smul _ _ _ hS]
  simp only [actualEnergyFluxDiv, actualEnergyFluxPdiv_eq_cartesianDiv,
    actualEnergyFluxRdiv_eq_cartesianDiv,
    actualEnergyFluxSdiv_eq_cartesianDiv]
  rfl

end SpringerLean

#print axioms SpringerLean.actualCartesianDiv_add
#print axioms SpringerLean.actualCartesianDiv_real_smul
#print axioms SpringerLean.actualCartesianDiv_sub
#print axioms SpringerLean.actualCartesianDiv_actualEnergyFluxField_eq
