import SpringerLean.Round1635EnergySplineTailDerivatives

namespace SpringerLean

/-- The three explicit multiplier compositions are differentiable at
every actual interior point whose time lies in an open affine cell. -/
theorem actualEnergyMultiplier_compositions_differentiableAt_cell
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (i : Fin 21)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (hleft : energyMultiplierKnotTime i.castSucc <
      actualHarmonicMultiplierTime F k z)
    (hright : actualHarmonicMultiplierTime F k z <
      energyMultiplierKnotTime i.succ) :
    DifferentiableAt ℝ
      (fun w => energyMultiplierChi
        (actualHarmonicMultiplierTime F k w)) z ∧
    DifferentiableAt ℝ
      (fun w => energyMultiplierF
        (actualHarmonicMultiplierTime F k w)) z ∧
    DifferentiableAt ℝ
      (fun w => energyMultiplierSigma
        (actualHarmonicMultiplierTime F k w)) z := by
  have ht := actualHarmonicMultiplierTime_differentiableAt
    F hc k hz hz0 hH
  have hs := energyMultiplierSpline_derivs_on_open_cell i
    (actualHarmonicMultiplierTime F k z) hleft hright
  exact ⟨hs.1.1.comp z ht, hs.2.1.1.comp z ht,
    hs.2.2.1.comp z ht⟩

/-- The same differentiability on the constant tail. -/
theorem actualEnergyMultiplier_compositions_differentiableAt_tail
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1)
    (hz0 : z ≠ 0) (hH : actualHarmonic F z ≠ 0)
    (htail : 1 < actualHarmonicMultiplierTime F k z) :
    DifferentiableAt ℝ
      (fun w => energyMultiplierChi
        (actualHarmonicMultiplierTime F k w)) z ∧
    DifferentiableAt ℝ
      (fun w => energyMultiplierF
        (actualHarmonicMultiplierTime F k w)) z ∧
    DifferentiableAt ℝ
      (fun w => energyMultiplierSigma
        (actualHarmonicMultiplierTime F k w)) z := by
  have ht := actualHarmonicMultiplierTime_differentiableAt
    F hc k hz hz0 hH
  have hs := energyMultiplierSpline_derivs_on_tail
    (actualHarmonicMultiplierTime F k z) htail
  exact ⟨hs.1.1.comp z ht, hs.2.1.1.comp z ht,
    hs.2.2.1.comp z ht⟩

end SpringerLean

#print axioms SpringerLean.actualEnergyMultiplier_compositions_differentiableAt_cell
#print axioms SpringerLean.actualEnergyMultiplier_compositions_differentiableAt_tail
