import SpringerLean.Round1977SeedProbabilityIntegral
import SpringerLean.Round1967SeedExteriorPotential

open MeasureTheory Metric Set

namespace SpringerLean

/-- The normalized seed boundary probability is carried by the actual
omitted continuum. -/
theorem oddStarSeed_boundary_probability_ae_omitted
    (t : ℝ) (ht : |t| < 1) :
    oddStarSeedOmitted t ∈ ae (oddStarSeedBoundaryProbability t) := by
  have hclosed : IsClosed (oddStarSeedOmitted t) :=
    (oddStarSeed_actual_continuum t ht).1.isClosed
  unfold oddStarSeedBoundaryProbability
  apply (mem_ae_map_iff
    (oddStarSeed_angle_continuous t ht).measurable.aemeasurable
    hclosed.measurableSet).2
  apply Filter.Eventually.of_forall
  intro θ
  rw [oddStarSeed_omitted_eq_boundary_image t ht]
  refine ⟨Complex.polarCoord.symm (1, θ), ?_, rfl⟩
  simp [oddStarSeedUnitCircle]

/-- The R1967 Jensen formula stated as the logarithmic potential of
the actual normalized seed boundary probability measure at each
exterior image point. -/
theorem oddStarSeed_boundary_probability_log_potential_exterior
    (t : ℝ) (ht : |t| < 1) (z : ℂ) (hz : 1 < ‖z‖) :
    (∫ w, Real.log ‖w - oddStarSeed t z‖
      ∂oddStarSeedBoundaryProbability t) = Real.log ‖z‖ := by
  let ζ : ℂ := oddStarSeed t z
  let K : Set ℂ := oddStarSeedOmitted t
  have hcompact : IsCompact K := (oddStarSeed_actual_continuum t ht).1
  have hKnonempty : K.Nonempty := ⟨0, oddStarSeed_zero_mem_omitted t ht⟩
  have hζnot : ζ ∉ K := by
    change oddStarSeed t z ∉ (oddStarSeed t '' exteriorDisk)ᶜ
    simp only [Set.mem_compl_iff, not_not]
    exact ⟨z, hz, rfl⟩
  let δ : ℝ := Metric.infDist ζ K
  have hδpos : 0 < δ :=
    (hcompact.isClosed.notMem_iff_infDist_pos hKnonempty).1 hζnot
  let φ : ℂ → ℝ := fun w => Real.log (max δ ‖w - ζ‖)
  have hφcont : Continuous φ := by
    have hnorm : Continuous (fun w : ℂ => ‖w - ζ‖) :=
      continuous_norm.comp (continuous_id.sub continuous_const)
    have hbase : Continuous (fun w : ℂ => max δ ‖w - ζ‖) :=
      continuous_const.max hnorm
    apply continuous_iff_continuousAt.mpr
    intro w
    have hmaxpos : 0 < max δ ‖w - ζ‖ :=
      lt_of_lt_of_le hδpos (le_max_left _ _)
    have hlog : ContinuousAt Real.log (max δ ‖w - ζ‖) :=
      Real.continuousAt_log hmaxpos.ne'
    exact ContinuousAt.comp
      (f := fun v : ℂ => max δ ‖v - ζ‖) hlog hbase.continuousAt
  have hφeq (w : ℂ) (hw : w ∈ K) : φ w = Real.log ‖w - ζ‖ := by
    have hle : δ ≤ ‖w - ζ‖ := by
      have h := Metric.infDist_le_dist_of_mem hw (x := ζ)
      simpa only [dist_eq_norm, norm_sub_rev] using h
    simp only [φ, max_eq_right hle]
  have hleft :
      (∫ w, Real.log ‖w - ζ‖ ∂oddStarSeedBoundaryProbability t) =
        ∫ w, φ w ∂oddStarSeedBoundaryProbability t := by
    apply integral_congr_ae
    filter_upwards [oddStarSeed_boundary_probability_ae_omitted t ht] with w hw
    exact (hφeq w hw).symm
  have hright :
      Real.circleAverage (fun u => φ (oddStarSeed t u)) 0 1 =
        Real.circleAverage (fun u => Real.log ‖oddStarSeed t u - ζ‖) 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro u hu
    have huK : oddStarSeed t u ∈ K := by
      change oddStarSeed t u ∈ oddStarSeedOmitted t
      rw [oddStarSeed_omitted_eq_boundary_image t ht]
      exact ⟨u, by simpa [oddStarSeedUnitCircle] using hu, rfl⟩
    exact hφeq _ huK
  calc
    (∫ w, Real.log ‖w - oddStarSeed t z‖
      ∂oddStarSeedBoundaryProbability t) = ∫ w, φ w ∂oddStarSeedBoundaryProbability t :=
      hleft
    _ = Real.circleAverage (fun u => φ (oddStarSeed t u)) 0 1 :=
      oddStarSeedBoundaryProbability_integral_eq_circleAverage t ht φ hφcont
    _ = Real.circleAverage
          (fun u => Real.log ‖oddStarSeed t u - oddStarSeed t z‖) 0 1 :=
      hright
    _ = Real.log ‖z‖ := oddStarSeed_boundary_log_potential_exterior t ht z hz

end SpringerLean

#print axioms SpringerLean.oddStarSeed_boundary_probability_log_potential_exterior
