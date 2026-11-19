import SpringerLean.Round1939FactorConstantDefinitions
import Mathlib.Analysis.Normed.Module.Connected

namespace SpringerLean

/-- The closed unit circle on which the seed's two critical preimages lie. -/
def oddStarSeedUnitCircle : Set ℂ := Metric.sphere 0 1

/-- The rational seed has no pole on its unit-circle boundary. -/
theorem oddStarSeed_denominator_ne_zero_on_circle
    (t : ℝ) (ht : |t| < 1) {z : ℂ}
    (hz : z ∈ oddStarSeedUnitCircle) :
    z - (t : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have hz' : z = (t : ℂ) * Complex.I := sub_eq_zero.mp hzero
  have hnorm : ‖z‖ = |t| := by
    rw [hz', norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs]
  have hcircle : ‖z‖ = 1 := by
    simpa [oddStarSeedUnitCircle, Metric.mem_sphere, dist_zero_right] using hz
  linarith

/-- The seed map extends continuously to the relevant boundary circle. -/
theorem oddStarSeed_continuousOn_circle
    (t : ℝ) (ht : |t| < 1) :
    ContinuousOn (oddStarSeed t) oddStarSeedUnitCircle := by
  unfold oddStarSeed
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro z hz
    exact oddStarSeed_denominator_ne_zero_on_circle t ht hz

/-- The boundary curve of the seed is connected, including at its two
critical points. This is the first half of the omitted-set identification. -/
theorem oddStarSeed_boundary_image_connected
    (t : ℝ) (ht : |t| < 1) :
    IsConnected (oddStarSeed t '' oddStarSeedUnitCircle) := by
  exact (isConnected_sphere (by simp) (0 : ℂ) (by norm_num)).image
    (oddStarSeed t) (oddStarSeed_continuousOn_circle t ht)

theorem oddStarSeed_zero_mem_boundary_image
    (t : ℝ) (ht : |t| < 1) :
    (0 : ℂ) ∈ oddStarSeed t '' oddStarSeedUnitCircle := by
  let s := Real.sqrt (1 - t ^ 2)
  refine ⟨(t : ℂ) * Complex.I - s, ?_, ?_⟩
  · simpa [oddStarSeedUnitCircle, Metric.mem_sphere, dist_zero_right, s] using
      (oddStarSeed_tip_norms t ht).1
  · exact (oddStarSeed_tip_values t ht).1

theorem oddStarSeed_outer_tip_mem_boundary_image
    (t : ℝ) (ht : |t| < 1) :
    ((4 * Real.sqrt (1 - t ^ 2) : ℝ) : ℂ) ∈
      oddStarSeed t '' oddStarSeedUnitCircle := by
  let s := Real.sqrt (1 - t ^ 2)
  refine ⟨(t : ℂ) * Complex.I + s, ?_, ?_⟩
  · simpa [oddStarSeedUnitCircle, Metric.mem_sphere, dist_zero_right, s] using
      (oddStarSeed_tip_norms t ht).2
  · exact (oddStarSeed_tip_values t ht).2

end SpringerLean

#print axioms SpringerLean.oddStarSeed_boundary_image_connected
#print axioms SpringerLean.oddStarSeed_zero_mem_boundary_image
#print axioms SpringerLean.oddStarSeed_outer_tip_mem_boundary_image
