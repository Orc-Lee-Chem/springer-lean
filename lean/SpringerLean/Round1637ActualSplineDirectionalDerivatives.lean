import SpringerLean.Round1636ActualSplineCompositions

namespace SpringerLean

theorem fderiv_outer_real_apply
    (f : ℝ → ℝ) (t : ℂ → ℝ) (z u : ℂ)
    (hf : DifferentiableAt ℝ f (t z))
    (ht : DifferentiableAt ℝ t z) :
    (fderiv ℝ (fun w => f (t w)) z) u =
      deriv f (t z)*(fderiv ℝ t z) u := by
  have h := (hf.hasDerivAt.comp_hasFDerivAt z ht.hasFDerivAt).fderiv
  have hu := congrArg (fun L : ℂ →L[ℝ] ℝ => L u) h
  change (fderiv ℝ (f ∘ t) z) u = _
  simpa only [smul_apply, smul_eq_mul] using hu

/-- Exact derivatives of the three explicit multipliers, composed
with the actual time, on every open printed cell. -/
theorem actualEnergyMultiplier_cell_directional_derivatives
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (i : Fin 21)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (hleft : energyMultiplierKnotTime i.castSucc <
      actualHarmonicMultiplierTime F k z)
    (hright : actualHarmonicMultiplierTime F k z <
      energyMultiplierKnotTime i.succ)
    (u : ℂ) :
    let t := actualHarmonicMultiplierTime F k
    let r := energyMultiplierEndpointRaw (2*i.val)
    (fderiv ℝ (fun w => energyMultiplierChi (t w)) z) u =
      (r.cp:ℝ)*(fderiv ℝ t z) u ∧
    (fderiv ℝ (fun w => energyMultiplierF (t w)) z) u =
      (r.fp:ℝ)*(fderiv ℝ t z) u ∧
    (fderiv ℝ (fun w => energyMultiplierSigma (t w)) z) u =
      (r.sp:ℝ)*(fderiv ℝ t z) u := by
  let t := actualHarmonicMultiplierTime F k
  have ht := actualHarmonicMultiplierTime_differentiableAt
    F hc k hz hz0 hH
  have hs := energyMultiplierSpline_derivs_on_open_cell i
    (t z) hleft hright
  refine ⟨?_, ?_, ?_⟩
  · rw [fderiv_outer_real_apply energyMultiplierChi t z u hs.1.1 ht,
      hs.1.2]
  · rw [fderiv_outer_real_apply energyMultiplierF t z u hs.2.1.1 ht,
      hs.2.1.2]
  · rw [fderiv_outer_real_apply energyMultiplierSigma t z u hs.2.2.1 ht,
      hs.2.2.2]

end SpringerLean

#print axioms SpringerLean.fderiv_outer_real_apply
#print axioms SpringerLean.actualEnergyMultiplier_cell_directional_derivatives
