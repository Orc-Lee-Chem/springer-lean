import SpringerLean.Round1980SeedGreenMeasure

open MeasureTheory Set

namespace SpringerLean

/-- The actual a.e. radial boundary law of every admissible odd-star
perturbation has total mass one. -/
theorem oddStarActualBoundaryProbability_univ
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    oddStarActualBoundaryProbability m t univ = 1 := by
  unfold oddStarActualBoundaryProbability
  have hf : AEMeasurable
      (actualExteriorRadialTrace (oddStarPerturbation m t))
      oddStarAngularProbability := by
    have hf0 : AEMeasurable
        (actualExteriorRadialTrace (oddStarPerturbation m t))
        oddStarAngularMeasure := (actualExteriorRadialTrace_aestronglyMeasurable
      (oddStarPerturbation m t)
      (oddStarPerturbation_centeredExteriorUnivalent m hm t ht)).aemeasurable
    unfold oddStarAngularProbability
    exact hf0.mono_ac Measure.smul_absolutelyContinuous
  rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ]
  simpa only [preimage_univ] using oddStarAngularProbability_univ

/-- The normalized actual radial boundary law is carried by the
actual omitted star continuum. -/
theorem oddStarPerturbation_actual_boundary_probability_ae_omitted
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    oddStarPerturbationOmitted m t ∈
      ae (oddStarActualBoundaryProbability m t) := by
  have hpow : AEMeasurable (fun z : ℂ => z ^ m)
      (oddStarActualBoundaryProbability m t) := by fun_prop
  have hseed : oddStarSeedOmitted t ∈
      ae ((oddStarActualBoundaryProbability m t).map
        (fun z : ℂ => z ^ m)) := by
    rw [oddStarPerturbation_actual_boundary_probability_map_pow m hm t ht]
    exact oddStarSeed_boundary_probability_ae_omitted t ht
  have hpre := mem_ae_of_mem_ae_map hpow hseed
  rw [oddStarPerturbation_omitted_eq_power_preimage m hm t ht]
  exact hpre

theorem oddStarPerturbation_actual_boundary_probability_support_subset
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    (oddStarActualBoundaryProbability m t).support ⊆
      oddStarPerturbationOmitted m t := by
  exact Measure.support_subset_of_isClosed
    (oddStarPerturbation_actual_continuum m hm t ht).1.isClosed
    (oddStarPerturbation_actual_boundary_probability_ae_omitted m hm t ht)

end SpringerLean

#print axioms SpringerLean.oddStarActualBoundaryProbability_univ
#print axioms SpringerLean.oddStarPerturbation_actual_boundary_probability_support_subset
