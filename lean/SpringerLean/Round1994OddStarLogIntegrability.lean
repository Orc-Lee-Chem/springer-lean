import SpringerLean.Round1993CyclicPowerDifference

open MeasureTheory Set Metric

namespace SpringerLean

/-- A logarithmic distance is integrable against a finite measure
carried by a compact set when its pole lies outside that set. -/
theorem log_distance_integrable_of_compact_support
    (K : Set ℂ) (hK : IsCompact K) (ν : Measure ℂ)
    [IsFiniteMeasure ν] (hν : K ∈ ae ν)
    (w : ℂ) (hw : w ∉ K) :
    Integrable (fun u : ℂ => Real.log ‖u - w‖) ν := by
  have hcont : ContinuousOn (fun u : ℂ => Real.log ‖u - w‖) K := by
    intro u hu
    have huw : u ≠ w := by
      intro heq
      exact hw (heq ▸ hu)
    have hnorm : ContinuousAt (fun v : ℂ => ‖v - w‖) u := by fun_prop
    have hnonzero : ‖u - w‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (sub_ne_zero.mpr huw)
    have hlog : ContinuousAt Real.log ‖u - w‖ :=
      Real.continuousAt_log hnonzero
    have hc : ContinuousAt (fun v : ℂ => Real.log ‖v - w‖) u :=
      ContinuousAt.comp (f := fun v : ℂ => ‖v - w‖) hlog hnorm
    exact hc.continuousWithinAt
  obtain ⟨M, hM⟩ :=
    (hK.image_of_continuousOn hcont).isBounded.exists_norm_le
  have hmeas : AEStronglyMeasurable
      (fun u : ℂ => Real.log ‖u - w‖) ν := by
    exact (Real.measurable_log.comp
      (measurable_norm.comp (measurable_id.sub measurable_const))).aestronglyMeasurable
  apply Integrable.of_bound hmeas M
  filter_upwards [hν] with u hu
  exact hM _ ⟨u, hu, rfl⟩

/-- The ordinary logarithmic distance to every point outside the
actual odd-star continuum is integrable against its actual radial
boundary probability. -/
theorem oddStarActualBoundaryProbability_log_distance_integrable
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    (w : ℂ) (hw : w ∉ oddStarPerturbationOmitted m t) :
    Integrable (fun u : ℂ => Real.log ‖u - w‖)
      (oddStarActualBoundaryProbability m t) := by
  haveI : IsFiniteMeasure (oddStarActualBoundaryProbability m t) :=
    Measure.isFiniteMeasure_map oddStarAngularProbability _
  exact log_distance_integrable_of_compact_support
    (oddStarPerturbationOmitted m t)
    (oddStarPerturbation_actual_continuum m hm t ht).1
    (oddStarActualBoundaryProbability m t)
    (oddStarPerturbation_actual_boundary_probability_ae_omitted m hm t ht)
    w hw

end SpringerLean

#print axioms SpringerLean.oddStarActualBoundaryProbability_log_distance_integrable
