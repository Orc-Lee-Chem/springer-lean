import SpringerLean.Round1988OddStarPowerGreenCoordinate

open MeasureTheory Set

namespace SpringerLean

/-- The normalized angular law, placed on the actual unit circle. -/
noncomputable def oddStarUnitCircleProbability : Measure ℂ :=
  oddStarAngularProbability.map
    (fun θ : ℝ => Complex.polarCoord.symm (1, θ))

theorem oddStarUnitCircleProbability_integral_eq_circleAverage
    (φ : ℂ → ℝ) (hφ : Continuous φ) :
    (∫ u, φ u ∂oddStarUnitCircleProbability) =
      Real.circleAverage φ 0 1 := by
  let g : ℝ → ℝ := fun θ => φ (Complex.polarCoord.symm (1, θ))
  have hgcont : Continuous g := by
    dsimp [g]
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  have hgperiod : Function.Periodic g (2 * Real.pi) := by
    intro θ
    exact congrArg φ (unitPolar_periodic θ)
  have hshift :
      (∫ θ in Ioo (-Real.pi) Real.pi, g θ) =
        ∫ θ in 0..2 * Real.pi, g θ := by
    have hset :
        (∫ θ in Ioo (-Real.pi) Real.pi, g θ) =
          ∫ θ in -Real.pi..Real.pi, g θ := by
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
        integral_Ioc_eq_integral_Ioo]
    rw [hset]
    convert hgperiod.intervalIntegral_add_eq (-Real.pi) 0 using 1 <;> ring_nf
  have hpolar : Measurable (fun θ : ℝ => Complex.polarCoord.symm (1, θ)) := by
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  unfold oddStarUnitCircleProbability oddStarAngularProbability
  rw [integral_map hpolar.aemeasurable hφ.aestronglyMeasurable]
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr (by positivity :
    0 < 2 * Real.pi))), smul_eq_mul]
  change (2 * Real.pi)⁻¹ *
      (∫ θ in Ioo (-Real.pi) Real.pi, g θ) =
        Real.circleAverage φ 0 1
  rw [hshift]
  unfold Real.circleAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [g, circleMap_zero, Complex.polarCoord_symm_apply]
  rw [Complex.exp_mul_I]
  simp

/-- The unit-circle probability is invariant under every angular rotation. -/
theorem oddStarUnitCircleProbability_map_rotation (δ : ℝ) :
    oddStarUnitCircleProbability.map
      (fun u : ℂ => Complex.polarCoord.symm (1, δ) * u) =
        oddStarUnitCircleProbability := by
  haveI : IsFiniteMeasure oddStarUnitCircleProbability :=
    Measure.isFiniteMeasure_map oddStarAngularProbability _
  haveI : IsFiniteMeasure
      (oddStarUnitCircleProbability.map
        (fun u : ℂ => Complex.polarCoord.symm (1, δ) * u)) :=
    Measure.isFiniteMeasure_map oddStarUnitCircleProbability _
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  have hrot : Measurable
      (fun u : ℂ => Complex.polarCoord.symm (1, δ) * u) := by fun_prop
  rw [integral_map hrot.aemeasurable φ.continuous.aestronglyMeasurable]
  rw [oddStarUnitCircleProbability_integral_eq_circleAverage
    (fun u => φ (Complex.polarCoord.symm (1, δ) * u))
      (φ.continuous.comp (by fun_prop))]
  rw [oddStarUnitCircleProbability_integral_eq_circleAverage φ φ.continuous]
  change Real.circleAverage
      (fun u => φ (Complex.polarCoord.symm (1, δ) * u)) 0 1 =
        Real.circleAverage φ 0 1
  rw [Real.circleAverage_def,
    Real.circleAverage_eq_integral_add (f := φ) (c := 0) (R := 1) δ]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [circleMap_zero, Complex.polarCoord_symm_apply]
  rw [← Complex.exp_ofReal_mul_I]
  simp only [Complex.ofReal_one, one_mul]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end SpringerLean

#print axioms SpringerLean.oddStarUnitCircleProbability_integral_eq_circleAverage
#print axioms SpringerLean.oddStarUnitCircleProbability_map_rotation
