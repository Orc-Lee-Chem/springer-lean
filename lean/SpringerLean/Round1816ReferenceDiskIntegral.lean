import SpringerLean.Round13Semicircle
import SpringerLean.Round1814ActualAllPhaseBudget
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Metric Set

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 700000

/-- A Bochner-integral version of the existing actual disk projection
law. It makes the reference tail an ordinary one-dimensional integral. -/
theorem comparisonDisk_re_integral_density (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, ψ z.re)=
      (2*Real.pi⁻¹)*(∫ x in Ioo (-1 : ℝ) 1, Real.sqrt (1-x^2)*ψ x) := by
  have hρ : Measurable comparisonDiskReDensity := by
    unfold comparisonDiskReDensity
    apply Measurable.ite
    · measurability
    · exact ENNReal.measurable_ofReal.comp (by fun_prop)
    · exact measurable_const
  have hfinite : ∀ᵐ x ∂(volume : Measure ℝ), comparisonDiskReDensity x < ⊤ := by
    filter_upwards [] with x
    unfold comparisonDiskReDensity
    split_ifs
    · exact ENNReal.ofReal_lt_top
    · exact bot_lt_top
  have hmap := integral_map_of_stronglyMeasurable
    (μ := volume.restrict (ball (0 : ℂ) 1)) Complex.measurable_re hψ.stronglyMeasurable
  rw [comparisonDisk_re_pushforward_density,
    integral_withDensity_eq_integral_toReal_smul hρ hfinite] at hmap
  have hpoint : (fun x : ℝ => (comparisonDiskReDensity x).toReal • ψ x)=
      (Ioo (-1 : ℝ) 1).indicator (fun x => 2*(Real.sqrt (1-x^2)*ψ x)) := by
    funext x
    by_cases hx : x ∈ Ioo (-1 : ℝ) 1
    · have hab : |x| < 1 := abs_lt.mpr hx
      simp only [comparisonDiskReDensity,if_pos hab,
        ENNReal.toReal_ofReal (show 0 ≤ 2*Real.sqrt (1-x^2) by positivity),
        smul_eq_mul,Set.indicator_of_mem hx]
      ring
    · have hab : ¬ |x| < 1 := fun hh => hx (abs_lt.mp hh)
      simp only [comparisonDiskReDensity,if_neg hab,ENNReal.toReal_zero,zero_smul,
        Set.indicator_of_notMem hx]
  rw [hpoint,integral_indicator measurableSet_Ioo,integral_const_mul] at hmap
  rw [←hmap]
  ring

end
end SpringerLean

#print axioms SpringerLean.comparisonDisk_re_integral_density
