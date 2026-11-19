import SpringerLean.Round1964OddBoundaryProbability

open MeasureTheory Set

namespace SpringerLean

/-- The normalized actual seed boundary distribution integrates every
continuous real test by the normalized unit-circle average. -/
theorem oddStarSeedBoundaryProbability_integral_eq_circleAverage
    (t : ℝ) (ht : |t| < 1) (φ : ℂ → ℝ) (hφ : Continuous φ) :
    (∫ w, φ w ∂oddStarSeedBoundaryProbability t) =
      Real.circleAverage (fun u => φ (oddStarSeed t u)) 0 1 := by
  let g : ℝ → ℝ := fun θ =>
    φ (oddStarSeed t (Complex.polarCoord.symm (1, θ)))
  have hgcont : Continuous g :=
    hφ.comp (oddStarSeed_angle_continuous t ht)
  have hgperiod : Function.Periodic g (2 * Real.pi) :=
    oddStarSeed_boundary_test_periodic t φ
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
  have hmap :
      (∫ w, φ w ∂oddStarSeedBoundaryProbability t) =
        (2 * Real.pi)⁻¹ *
          (∫ θ in Ioo (-Real.pi) Real.pi, g θ) := by
    unfold oddStarSeedBoundaryProbability oddStarAngularProbability
    rw [integral_map
      (oddStarSeed_angle_continuous t ht).measurable.aemeasurable
      hφ.aestronglyMeasurable]
    rw [integral_smul_measure]
    simp only [ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr (by positivity :
      0 < 2 * Real.pi)))]
    simp only [smul_eq_mul]
    rfl
  rw [hmap, hshift]
  unfold Real.circleAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [g, circleMap_zero, Complex.polarCoord_symm_apply]
  rw [Complex.exp_mul_I]
  simp

end SpringerLean

#print axioms SpringerLean.oddStarSeedBoundaryProbability_integral_eq_circleAverage
