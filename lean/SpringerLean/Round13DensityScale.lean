import SpringerLean.Round13Density
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory Set

namespace SpringerLean

private theorem map_double_volume :
    Measure.map (fun x : ℝ => 2 * x) volume =
      ENNReal.ofReal (1 / 2 : ℝ) • volume := by
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (by fun_prop) hB,
    Real.volume_preimage_mul_left (a := (2 : ℝ)) (by norm_num),
    Measure.smul_apply]
  norm_num

theorem map_double_withDensity (f : ℝ → ENNReal) (hf : Measurable f) :
    Measure.map (fun x : ℝ => 2 * x) ((volume : Measure ℝ).withDensity f) =
      (volume : Measure ℝ).withDensity
        (fun y => ENNReal.ofReal (1 / 2 : ℝ) * f (y / 2)) := by
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (by fun_prop) hB,
    withDensity_apply f (hB.preimage (by fun_prop)),
    withDensity_apply _ hB]
  rw [← lintegral_indicator (hB.preimage (by fun_prop)),
    ← lintegral_indicator hB]
  have htest : Measurable (fun y : ℝ => B.indicator (fun y => f (y / 2)) y) :=
    (hf.comp (by fun_prop)).indicator hB
  calc
    (∫⁻ x : ℝ, ((fun t : ℝ => 2 * t) ⁻¹' B).indicator f x ∂volume) =
      ∫⁻ y : ℝ, B.indicator (fun y => f (y / 2)) y
        ∂Measure.map (fun x : ℝ => 2 * x) volume := by
          rw [lintegral_map htest (by fun_prop)]
          congr 1
          funext x
          have hdiv : 2 * x / 2 = x := by ring
          by_cases hx : 2 * x ∈ B
          · simp [Set.indicator, hx, hdiv]
          · simp [Set.indicator, hx, hdiv]
    _ = ∫⁻ y : ℝ, B.indicator (fun y => f (y / 2)) y
        ∂(ENNReal.ofReal (1 / 2 : ℝ) • volume) := by rw [map_double_volume]
    _ = ENNReal.ofReal (1 / 2 : ℝ) *
        ∫⁻ y : ℝ, B.indicator (fun y => f (y / 2)) y ∂volume := by
          rw [lintegral_smul_measure]
          rfl
    _ = ∫⁻ y : ℝ, B.indicator
        (fun y => ENNReal.ofReal (1 / 2 : ℝ) * f (y / 2)) y ∂volume := by
          rw [← lintegral_const_mul _ htest]
          congr 1
          funext y
          by_cases hy : y ∈ B <;> simp [Set.indicator, hy]

end SpringerLean