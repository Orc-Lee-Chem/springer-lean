import SpringerLean.Round1698FiniteRampSumLipschitz
import SpringerLean.Round1625EnergySplineCellValues

namespace SpringerLean

/-- All three printed multipliers vanish at physical time zero. -/
theorem energyMultipliers_zero :
    energyMultiplierChi 0 = 0 ∧
    energyMultiplierF 0 = 0 ∧
    energyMultiplierSigma 0 = 0 := by
  have hvals := energyMultiplierSpline_on_cell (0 : Fin 21) 0
    (by norm_num [energyMultiplierKnotTime,
      energyMultiplierEndpointRaw, energyMultiplierNode])
    (by norm_num [energyMultiplierKnotTime,
      energyMultiplierEndpointRaw, energyMultiplierNode])
  norm_num [energyMultiplierKnotTime,
    energyMultiplierEndpointRaw, energyMultiplierNode] at hvals
  exact hvals

/-- A Lipschitz multiplier vanishing at zero has an explicit linear
bound in the physical time. -/
theorem lipschitz_zero_linear_bound
    (φ : ℝ → ℝ) {C : NNReal}
    (hφ : LipschitzWith C φ) (hzero : φ 0 = 0) (t : ℝ) :
    |φ t| ≤ (C : ℝ) * |t| := by
  have h := hφ.dist_le_mul t 0
  simpa only [Real.dist_eq, sub_zero, hzero] using h

theorem energyMultiplierChi_linear_bound (t : ℝ) :
    |energyMultiplierChi t| ≤
      (↑(∑ i : Fin 21,
        (⟨2 * |((energyMultiplierEndpointRaw (2 * i.val)).cp : ℝ)|,
          by positivity⟩ : NNReal)) : ℝ) * |t| :=
  lipschitz_zero_linear_bound energyMultiplierChi
    energyMultiplierChi_lipschitz energyMultipliers_zero.1 t

theorem energyMultiplierF_linear_bound (t : ℝ) :
    |energyMultiplierF t| ≤
      (↑(∑ i : Fin 21,
        (⟨2 * |((energyMultiplierEndpointRaw (2 * i.val)).fp : ℝ)|,
          by positivity⟩ : NNReal)) : ℝ) * |t| :=
  lipschitz_zero_linear_bound energyMultiplierF
    energyMultiplierF_lipschitz energyMultipliers_zero.2.1 t

theorem energyMultiplierSigma_linear_bound (t : ℝ) :
    |energyMultiplierSigma t| ≤
      (↑(∑ i : Fin 21,
        (⟨2 * |((energyMultiplierEndpointRaw (2 * i.val)).sp : ℝ)|,
          by positivity⟩ : NNReal)) : ℝ) * |t| :=
  lipschitz_zero_linear_bound energyMultiplierSigma
    energyMultiplierSigma_lipschitz energyMultipliers_zero.2.2 t

end SpringerLean

#print axioms SpringerLean.energyMultipliers_zero
#print axioms SpringerLean.lipschitz_zero_linear_bound
#print axioms SpringerLean.energyMultiplierChi_linear_bound
#print axioms SpringerLean.energyMultiplierF_linear_bound
#print axioms SpringerLean.energyMultiplierSigma_linear_bound
