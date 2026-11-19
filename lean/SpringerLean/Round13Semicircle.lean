import SpringerLean.Round13DensityScale

open MeasureTheory Metric

namespace SpringerLean

noncomputable def comparisonDiskProbability : Measure ℂ :=
  ENNReal.ofReal (Real.pi⁻¹) • volume.restrict (ball (0 : ℂ) 1)

private theorem comparisonDiskReDensity_measurable :
    Measurable comparisonDiskReDensity := by
  unfold comparisonDiskReDensity
  apply Measurable.ite
  · measurability
  · exact ENNReal.measurable_ofReal.comp (by fun_prop)
  · exact measurable_const

/-- The normalized unit-disk law under `2 Re z`, before simplifying its
explicit density to the standard semicircle expression. -/
theorem comparisonDisk_two_re_pushforward_density :
    Measure.map (fun z : ℂ => 2 * z.re) comparisonDiskProbability =
      (volume : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal (Real.pi⁻¹) *
          (ENNReal.ofReal (1 / 2 : ℝ) * comparisonDiskReDensity (x / 2))) := by
  unfold comparisonDiskProbability
  change Measure.map ((fun x : ℝ => 2 * x) ∘ (fun z : ℂ => z.re))
      (ENNReal.ofReal Real.pi⁻¹ • volume.restrict (ball (0 : ℂ) 1)) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [Measure.map_smul _ (by fun_prop)]
  rw [comparisonDisk_re_pushforward_density]
  rw [Measure.map_smul _ (by fun_prop)]
  rw [map_double_withDensity comparisonDiskReDensity comparisonDiskReDensity_measurable]
  rw [← withDensity_smul' (μ := (volume : Measure ℝ))
    (ENNReal.ofReal Real.pi⁻¹)
    (fun x => ENNReal.ofReal (1 / 2 : ℝ) * comparisonDiskReDensity (x / 2))
    (by simp)]
  rfl


/-- The standard compactly supported semicircle density. -/
noncomputable def comparisonSemicircleDensity (x : ℝ) : ENNReal :=
  if |x| < 2 then
    ENNReal.ofReal (Real.sqrt (4 - x ^ 2) / (2 * Real.pi))
  else 0

theorem comparisonSemicircleDensity_eq_scaled (x : ℝ) :
    ENNReal.ofReal (Real.pi⁻¹) *
      (ENNReal.ofReal (1 / 2 : ℝ) * comparisonDiskReDensity (x / 2)) =
    comparisonSemicircleDensity x := by
  have hhalf : |x / 2| < 1 ↔ |x| < 2 := by
    rw [abs_div]
    norm_num
    constructor <;> intro h <;> nlinarith
  by_cases hx : |x| < 2
  · have hxhalf : |x / 2| < 1 := hhalf.mpr hx
    have hsqrt : Real.sqrt (4 - x ^ 2) =
        2 * Real.sqrt (1 - (x / 2) ^ 2) := by
      have hfactor : 4 - x ^ 2 = 4 * (1 - (x / 2) ^ 2) := by ring
      have h4 : Real.sqrt (4 : ℝ) = 2 := by
        convert Real.sqrt_sq_eq_abs (2 : ℝ) using 1 <;> norm_num
      rw [hfactor, Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)), h4]
    have hreal : Real.pi⁻¹ * ((1 / 2 : ℝ) *
        (2 * Real.sqrt (1 - (x / 2) ^ 2))) =
        Real.sqrt (4 - x ^ 2) / (2 * Real.pi) := by
      rw [hsqrt]
      field_simp [Real.pi_pos.ne']
    simp only [comparisonDiskReDensity, comparisonSemicircleDensity,
      if_pos hxhalf, if_pos hx]
    rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr Real.pi_pos))]
    exact congrArg ENNReal.ofReal hreal
  · have hxhalf : ¬|x / 2| < 1 := fun h => hx (hhalf.mp h)
    simp [comparisonDiskReDensity, comparisonSemicircleDensity, hx, hxhalf]

/-- The normalized disk comparison variable has the exact semicircle law. -/
theorem comparisonDisk_two_re_semicircle_law :
    Measure.map (fun z : ℂ => 2 * z.re) comparisonDiskProbability =
      (volume : Measure ℝ).withDensity comparisonSemicircleDensity := by
  rw [comparisonDisk_two_re_pushforward_density]
  congr 1
  funext x
  exact comparisonSemicircleDensity_eq_scaled x

/-- The area normalization used for the semicircle law has mass one. -/
theorem comparisonDiskProbability_univ :
    comparisonDiskProbability Set.univ = 1 := by
  unfold comparisonDiskProbability
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter]
  rw [Complex.volume_ball]
  norm_num
  rw [← ENNReal.ofReal_coe_nnreal]
  change ENNReal.ofReal Real.pi⁻¹ * ENNReal.ofReal Real.pi = 1
  rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr Real.pi_pos))]
  simp [Real.pi_pos.ne']
end SpringerLean