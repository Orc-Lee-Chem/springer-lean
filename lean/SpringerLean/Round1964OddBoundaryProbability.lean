import SpringerLean.Round1963OddBoundarySupport

open MeasureTheory Set

namespace SpringerLean

/-- The normalized angular law on one centered turn. -/
noncomputable def oddStarAngularProbability : Measure ℝ :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹) • oddStarAngularMeasure

theorem oddStarAngularProbability_univ :
    oddStarAngularProbability univ = 1 := by
  unfold oddStarAngularProbability oddStarAngularMeasure
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ]
  simp only [univ_inter]
  rw [Real.volume_Ioo]
  have hsub : Real.pi - -Real.pi = 2 * Real.pi := by ring
  rw [hsub]
  change ENNReal.ofReal ((2 * Real.pi)⁻¹) *
    ENNReal.ofReal (2 * Real.pi) = 1
  rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr (by positivity)))]
  rw [inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0)]
  simp

instance : IsProbabilityMeasure oddStarAngularProbability :=
  ⟨oddStarAngularProbability_univ⟩

/-- The normalized actual radial boundary distribution. -/
noncomputable def oddStarActualBoundaryProbability
    (m : ℕ) (t : ℝ) : Measure ℂ :=
  oddStarAngularProbability.map
    (actualExteriorRadialTrace (oddStarPerturbation m t))

/-- The normalized seed boundary distribution. -/
noncomputable def oddStarSeedBoundaryProbability
    (t : ℝ) : Measure ℂ :=
  oddStarAngularProbability.map
    (fun θ => oddStarSeed t (Complex.polarCoord.symm (1, θ)))

/-- Probability-level power pushforward for the actual radial trace. -/
theorem oddStarPerturbation_actual_boundary_probability_map_pow
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    (oddStarActualBoundaryProbability m t).map (fun z : ℂ => z ^ m) =
      oddStarSeedBoundaryProbability t := by
  let c : ENNReal := ENNReal.ofReal ((2 * Real.pi)⁻¹)
  have hf : AEMeasurable
      (actualExteriorRadialTrace (oddStarPerturbation m t))
      oddStarAngularMeasure := by
    exact (actualExteriorRadialTrace_aestronglyMeasurable
      (oddStarPerturbation m t)
      (oddStarPerturbation_centeredExteriorUnivalent m hm t ht)).aemeasurable
  have hg : AEMeasurable
      (fun θ => oddStarSeed t (Complex.polarCoord.symm (1, θ)))
      oddStarAngularMeasure :=
    (oddStarSeed_angle_continuous t ht).measurable.aemeasurable
  have hpow : AEMeasurable (fun z : ℂ => z ^ m)
      (oddStarActualBoundaryMeasure m t) := by fun_prop
  unfold oddStarActualBoundaryProbability oddStarSeedBoundaryProbability
    oddStarAngularProbability
  rw [Measure.map_smul c hf, Measure.map_smul c hg]
  change (c • oddStarActualBoundaryMeasure m t).map
    (fun z : ℂ => z ^ m) = c • oddStarSeedBoundaryMeasure t
  rw [Measure.map_smul c hpow]
  exact congrArg (c • ·)
    (oddStarPerturbation_actual_boundary_measure_map_pow m hm t ht)

end SpringerLean

#print axioms SpringerLean.oddStarAngularProbability_univ
#print axioms SpringerLean.oddStarPerturbation_actual_boundary_probability_map_pow
