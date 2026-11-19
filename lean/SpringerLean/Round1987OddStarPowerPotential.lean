import SpringerLean.Round1986OddStarBoundaryProbabilitySupport

open MeasureTheory Set

namespace SpringerLean

/-- The actual odd-star radial boundary probability has the seed Green
potential after the power map.  The test is logarithmic and is evaluated
at every point outside the actual seed omitted continuum. -/
theorem oddStarActualBoundaryProbability_power_log_potential_outside
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    (w : ℂ) (hw : w ∉ oddStarSeedOmitted t) :
    ∃ z : ℂ, 1 < ‖z‖ ∧ oddStarSeed t z = w ∧
      (∫ u, Real.log ‖u ^ m - w‖
        ∂oddStarActualBoundaryProbability m t) = Real.log ‖z‖ := by
  obtain ⟨z, hz, hzw, hpot⟩ :=
    oddStarSeed_boundary_probability_log_potential_outside t ht w hw
  refine ⟨z, hz, hzw, ?_⟩
  have hpow : AEMeasurable (fun u : ℂ => u ^ m)
      (oddStarActualBoundaryProbability m t) := by fun_prop
  have hlog : AEStronglyMeasurable
      (fun v : ℂ => Real.log ‖v - w‖)
      ((oddStarActualBoundaryProbability m t).map (fun u : ℂ => u ^ m)) := by
    exact (Real.measurable_log.comp
      (measurable_norm.comp (measurable_id.sub measurable_const))).aestronglyMeasurable
  calc
    (∫ u, Real.log ‖u ^ m - w‖
      ∂oddStarActualBoundaryProbability m t) =
        ∫ v, Real.log ‖v - w‖
          ∂(oddStarActualBoundaryProbability m t).map
            (fun u : ℂ => u ^ m) := by
              exact (integral_map hpow hlog).symm
    _ = ∫ v, Real.log ‖v - w‖
          ∂oddStarSeedBoundaryProbability t := by
            rw [oddStarPerturbation_actual_boundary_probability_map_pow
              m hm t ht]
    _ = Real.log ‖z‖ := hpot

end SpringerLean

#print axioms SpringerLean.oddStarActualBoundaryProbability_power_log_potential_outside
