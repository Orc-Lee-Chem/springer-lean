import SpringerLean.Round1962OddBoundaryMeasure
import Mathlib.MeasureTheory.Measure.Support

open MeasureTheory Set

namespace SpringerLean

/-- The seed's actual angular boundary measure is carried by the
geometric omitted continuum. -/
theorem oddStarSeed_boundary_measure_ae_omitted
    (t : ℝ) (ht : |t| < 1) :
    oddStarSeedOmitted t ∈ ae (oddStarSeedBoundaryMeasure t) := by
  have hclosed : IsClosed (oddStarSeedOmitted t) :=
    (oddStarSeed_actual_continuum t ht).1.isClosed
  unfold oddStarSeedBoundaryMeasure
  apply (mem_ae_map_iff
    (oddStarSeed_angle_continuous t ht).measurable.aemeasurable
    hclosed.measurableSet).2
  apply Filter.Eventually.of_forall
  intro θ
  rw [oddStarSeed_omitted_eq_boundary_image t ht]
  refine ⟨Complex.polarCoord.symm (1, θ), ?_, rfl⟩
  simp [oddStarSeedUnitCircle]

/-- The actual radial boundary distribution of the star perturbation
is carried by its actual omitted continuum. This follows from the
measure-level power identity and the exact power-preimage geometry. -/
theorem oddStarPerturbation_actual_boundary_measure_ae_omitted
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    oddStarPerturbationOmitted m t ∈
      ae (oddStarActualBoundaryMeasure m t) := by
  have hpow : AEMeasurable (fun z : ℂ => z ^ m)
      (oddStarActualBoundaryMeasure m t) := by
    fun_prop
  have hseed : oddStarSeedOmitted t ∈
      ae ((oddStarActualBoundaryMeasure m t).map
        (fun z : ℂ => z ^ m)) := by
    rw [oddStarPerturbation_actual_boundary_measure_map_pow m hm t ht]
    exact oddStarSeed_boundary_measure_ae_omitted t ht
  have hpre := mem_ae_of_mem_ae_map hpow hseed
  rw [oddStarPerturbation_omitted_eq_power_preimage m hm t ht]
  exact hpre

theorem oddStarSeed_boundary_measure_support_subset
    (t : ℝ) (ht : |t| < 1) :
    (oddStarSeedBoundaryMeasure t).support ⊆ oddStarSeedOmitted t := by
  exact Measure.support_subset_of_isClosed
    (oddStarSeed_actual_continuum t ht).1.isClosed
    (oddStarSeed_boundary_measure_ae_omitted t ht)

theorem oddStarPerturbation_actual_boundary_measure_support_subset
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    (oddStarActualBoundaryMeasure m t).support ⊆
      oddStarPerturbationOmitted m t := by
  exact Measure.support_subset_of_isClosed
    (oddStarPerturbation_actual_continuum m hm t ht).1.isClosed
    (oddStarPerturbation_actual_boundary_measure_ae_omitted m hm t ht)

end SpringerLean

#print axioms SpringerLean.oddStarSeed_boundary_measure_support_subset
#print axioms SpringerLean.oddStarPerturbation_actual_boundary_measure_support_subset
