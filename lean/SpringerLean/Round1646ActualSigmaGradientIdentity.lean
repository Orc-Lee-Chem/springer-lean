import SpringerLean.Round1645ActualChiGradientCancellation

open scoped ComplexConjugate

namespace SpringerLean

/-- Exact sigma-cutoff derivative in the actual S flux, kept signed
until the three fluxes have been combined. -/
theorem actualEnergyMultiplier_sigma_gradient_identity
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) (i : Fin 21)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (hleft : energyMultiplierKnotTime i.castSucc <
      actualHarmonicMultiplierTime F k z)
    (hright : actualHarmonicMultiplierTime F k z <
      energyMultiplierKnotTime i.succ) :
    let U := actualHarmonicPhaseField F k beta
    let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
    let t := actualHarmonicMultiplierTime F k
    let sigma : ℂ → ℝ := fun w => energyMultiplierSigma (t w)
    let sp : ℝ := (energyMultiplierEndpointRaw (2*i.val)).sp
    let Q : ℂ := (conj (actualHarmonic F z))⁻¹
    (U z)^2 *
      ((fderiv ℝ sigma z) (1:ℂ)*Q.re +
       (fderiv ℝ sigma z) Complex.I*Q.im) =
      -sp*(U z)^2/y z *
        ((k:ℝ)*
          ((fderiv ℝ (fun w : ℂ => ‖w‖) z) (1:ℂ)*Q.re +
           (fderiv ℝ (fun w : ℂ => ‖w‖) z) Complex.I*Q.im) +
         t z*
          ((fderiv ℝ y z) (1:ℂ)*Q.re +
           (fderiv ℝ y z) Complex.I*Q.im)) := by
  have hs1 := (actualEnergyMultiplier_cell_directional_derivatives
    F hc k i hz hz0 hH hleft hright (1:ℂ)).2.2
  have hsI := (actualEnergyMultiplier_cell_directional_derivatives
    F hc k i hz hz0 hH hleft hright Complex.I).2.2
  have ht1 := actualHarmonicMultiplierTime_fderiv
    F hc k hz hz0 hH (1:ℂ)
  have htI := actualHarmonicMultiplierTime_fderiv
    F hc k hz hz0 hH Complex.I
  have hy0 : ‖actualHarmonic F z‖ ≠ 0 := norm_ne_zero_iff.mpr hH
  dsimp only at hs1 hsI ht1 htI ⊢
  rw [hs1,hsI,ht1,htI]
  field_simp [hy0]
  ring

end SpringerLean

#print axioms SpringerLean.actualEnergyMultiplier_sigma_gradient_identity
