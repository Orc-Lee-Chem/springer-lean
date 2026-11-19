import SpringerLean.Round1696LipschitzFlatComposition
import SpringerLean.Round1618EnergyMultiplierSpline
import Mathlib.Analysis.Normed.Group.AddTorsor

namespace SpringerLean

theorem shiftedIdentity_lipschitz (a : ℝ) :
    LipschitzWith 1 (fun t : ℝ => t - a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  have h : (x - a) - (y - a) = x - y := by ring
  rw [h]

theorem positiveShift_lipschitz (a : ℝ) :
    LipschitzWith 1 (fun t : ℝ => max 0 (t - a)) := by
  simpa using (LipschitzWith.const (0 : ℝ)).max
    (shiftedIdentity_lipschitz a)

theorem energyMultiplierRamp_lipschitz (a b : ℝ) :
    LipschitzWith 2 (energyMultiplierRamp a b) := by
  convert (positiveShift_lipschitz a).vsub
    (positiveShift_lipschitz b) using 1
  · norm_num
  · funext t
    simp [energyMultiplierRamp, Pi.vsub_apply]

end SpringerLean

#print axioms SpringerLean.energyMultiplierRamp_lipschitz
