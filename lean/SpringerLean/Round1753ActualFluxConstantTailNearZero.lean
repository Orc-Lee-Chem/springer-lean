import SpringerLean.Round1746ActualTimeLocalLipschitz

open Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

/-- Near a noncentral filling zero, each actual flux agrees with the
corresponding constant-tail formula, including at all other filling
zeros in that neighbourhood. -/
theorem actualEnergyFluxFields_constant_tail_near_filling_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hzero : actualHarmonic F z = 0) :
    ∃ a b c : ℝ, ∀ᶠ w in 𝓝 z,
      let U := actualHarmonicPhaseField F k beta
      actualEnergyFluxPField F k beta w =
        Complex.mk (a*U w*(fderiv ℝ U w) (1 : ℂ))
          (a*U w*(fderiv ℝ U w) Complex.I) ∧
      actualEnergyFluxRField F k beta w =
        Complex.mk ((b*(U w)^2/‖actualHarmonic F w‖)*w.re/‖w‖)
          ((b*(U w)^2/‖actualHarmonic F w‖)*w.im/‖w‖) ∧
      actualEnergyFluxSField F k beta w =
        Complex.mk (c*(U w)^2*((conj (actualHarmonic F w))⁻¹).re)
          (c*(U w)^2*((conj (actualHarmonic F w))⁻¹).im) := by
  let a : ℝ := (energyMultiplierEndpointRaw 42).chi
  let b : ℝ := (energyMultiplierEndpointRaw 42).f
  let c : ℝ := (energyMultiplierEndpointRaw 42).sigma
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpos : 0 < (k : ℝ)*(1-‖z‖)-‖actualHarmonic F z‖ := by
    rw [hzero, norm_zero, sub_zero]
    exact mul_pos hkpos (sub_pos.mpr hz)
  have hcpos : ContinuousAt
      (fun w => (k : ℝ)*(1-‖w‖)-‖actualHarmonic F w‖) z :=
    (continuousAt_const.mul (continuousAt_const.sub continuous_norm.continuousAt)).sub
      (actualHarmonic_contDiffAt_real F hc hz).continuousAt.norm
  have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  refine ⟨a, b, c, ?_⟩
  filter_upwards [hcpos.eventually (lt_mem_nhds hpos),
    Metric.isOpen_ball.mem_nhds hzball] with w hw hwball
  have hw' : ‖w‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hwball
  by_cases hH : actualHarmonic F w = 0
  · have hU := (actualHarmonicPhaseField_zero_and_fderiv_zero
      F hc k hk beta hw' hH).1
    dsimp only
    constructor
    · apply Complex.ext <;> simp [actualEnergyFluxPField, hU]
    constructor
    · apply Complex.ext <;> simp [actualEnergyFluxRField, hU]
    · apply Complex.ext <;> simp [actualEnergyFluxSField, hU]
  · have ht : 1 < actualHarmonicMultiplierTime F k w := by
      dsimp [actualHarmonicMultiplierTime]
      apply (lt_div_iff₀ (norm_pos_iff.mpr hH)).mpr
      linarith
    have htail := energyMultiplierSpline_tail (actualHarmonicMultiplierTime F k w)
      (by rw [energyMultiplierKnotTime_last]; exact ht.le)
    dsimp only
    simp only [actualEnergyFluxPField, actualEnergyFluxRField,
      actualEnergyFluxSField, htail.1, htail.2.1, htail.2.2]
    exact ⟨rfl, rfl, rfl⟩

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxFields_constant_tail_near_filling_zero
