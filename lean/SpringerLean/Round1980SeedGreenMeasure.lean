import SpringerLean.Round1978SeedMeasurePotential

open MeasureTheory Set Metric

namespace SpringerLean

/-- The actual normalized seed boundary measure has total mass one. -/
theorem oddStarSeedBoundaryProbability_univ
    (t : ℝ) (ht : |t| < 1) :
    oddStarSeedBoundaryProbability t univ = 1 := by
  unfold oddStarSeedBoundaryProbability
  rw [Measure.map_apply
    (oddStarSeed_angle_continuous t ht).measurable MeasurableSet.univ]
  simpa only [preimage_univ] using oddStarAngularProbability_univ

/-- The seed potential theorem stated at an arbitrary point in the
actual exterior of its omitted continuum. The inverse preimage comes
from the defining image complement, and the potential value is its
logarithmic exterior coordinate. -/
theorem oddStarSeed_boundary_probability_log_potential_outside
    (t : ℝ) (ht : |t| < 1) (w : ℂ)
    (hw : w ∉ oddStarSeedOmitted t) :
    ∃ z : ℂ, 1 < ‖z‖ ∧ oddStarSeed t z = w ∧
      (∫ u, Real.log ‖u - w‖
        ∂oddStarSeedBoundaryProbability t) = Real.log ‖z‖ := by
  have hmem : w ∈ oddStarSeed t '' exteriorDisk := by
    simpa only [oddStarSeedOmitted, Set.mem_compl_iff, not_not] using hw
  rcases hmem with ⟨z, hz, rfl⟩
  refine ⟨z, hz, rfl, ?_⟩
  exact oddStarSeed_boundary_probability_log_potential_exterior t ht z hz

end SpringerLean

#print axioms SpringerLean.oddStarSeedBoundaryProbability_univ
#print axioms SpringerLean.oddStarSeed_boundary_probability_log_potential_outside
