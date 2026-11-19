import SpringerLean.Round1989CircleProbabilityRotation

open MeasureTheory Set

namespace SpringerLean

/-- The image probability of an actual smooth exterior circle under the
odd-star perturbation.  The radius is s⁻¹ > 1. -/
noncomputable def oddStarOuterCircleProbability
    (m : ℕ) (t s : ℝ) : Measure ℂ :=
  oddStarUnitCircleProbability.map
    (fun u : ℂ => oddStarPerturbation m t ((s⁻¹ : ℂ) * u))

/-- Every fixed smooth outer-circle image law is invariant under each
m-th-root rotation.  This is an exact equality of actual measures. -/
theorem oddStarOuterCircleProbability_map_rotation
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    (s : ℝ) (hs : 0 < s ∧ s < 1)
    (δ : ℝ)
    (hη : (Complex.polarCoord.symm (1, δ) : ℂ) ^ m = 1) :
    (oddStarOuterCircleProbability m t s).map
      (fun u : ℂ => Complex.polarCoord.symm (1, δ) * u) =
        oddStarOuterCircleProbability m t s := by
  let η : ℂ := Complex.polarCoord.symm (1, δ)
  let f : ℂ → ℂ := fun u => oddStarPerturbation m t ((s⁻¹ : ℂ) * u)
  have hFs : ContinuousOn (oddStarPerturbation m t) exteriorDisk :=
    (oddStarPerturbation_centeredExteriorUnivalent m hm t ht).1.continuousOn
  have hfcont : ContinuousOn f (Metric.sphere (0 : ℂ) 1) := by
    apply hFs.comp
    · fun_prop
    · intro u hu
      have hunorm : ‖u‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hu
      change 1 < ‖(s⁻¹ : ℂ) * u‖
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs.1, hunorm, mul_one]
      exact (one_lt_inv₀ hs.1).mpr hs.2
  have hfs : AEMeasurable f oddStarUnitCircleProbability := by
    have hsupport : Metric.sphere (0 : ℂ) 1 ∈
        ae oddStarUnitCircleProbability := by
      unfold oddStarUnitCircleProbability
      apply (mem_ae_map_iff
        (show Measurable (fun θ : ℝ =>
          Complex.polarCoord.symm (1, θ)) by
            simp_rw [Complex.polarCoord_symm_apply]
            fun_prop).aemeasurable
        Metric.isClosed_sphere.measurableSet).2
      filter_upwards with θ
      simp
    have hfs0 := hfcont.aemeasurable
      (μ := oddStarUnitCircleProbability)
      Metric.isClosed_sphere.measurableSet
    have heq : oddStarUnitCircleProbability.restrict
        (Metric.sphere (0 : ℂ) 1) = oddStarUnitCircleProbability :=
      Measure.restrict_eq_self_of_ae_mem hsupport
    simpa only [heq] using hfs0
  have hrot : Measurable (fun u : ℂ => η * u) := by fun_prop
  have hfsrot : AEMeasurable f
      (oddStarUnitCircleProbability.map (fun u : ℂ => η * u)) := by
    change AEMeasurable f
      (oddStarUnitCircleProbability.map
        (fun u : ℂ => Complex.polarCoord.symm (1, δ) * u))
    rw [oddStarUnitCircleProbability_map_rotation δ]
    exact hfs
  have hfun (u : ℂ) : η * f u = f (η * u) := by
    dsimp [f]
    rw [show (s⁻¹ : ℂ) * (η * u) = η * ((s⁻¹ : ℂ) * u) by ring]
    exact (oddStarPerturbation_rotation m t η ((s⁻¹ : ℂ) * u) hη).symm
  change (oddStarUnitCircleProbability.map f).map (fun u => η * u) =
    oddStarUnitCircleProbability.map f
  calc
    (oddStarUnitCircleProbability.map f).map (fun u => η * u) =
        oddStarUnitCircleProbability.map (fun u => η * f u) := by
          exact AEMeasurable.map_map_of_aemeasurable
            hrot.aemeasurable hfs
    _ = oddStarUnitCircleProbability.map (fun u => f (η * u)) := by
          congr 1
          funext u
          exact hfun u
    _ = (oddStarUnitCircleProbability.map (fun u => η * u)).map f := by
          exact (AEMeasurable.map_map_of_aemeasurable
            hfsrot hrot.aemeasurable).symm
    _ = oddStarUnitCircleProbability.map f := by
          rw [oddStarUnitCircleProbability_map_rotation δ]

end SpringerLean

#print axioms SpringerLean.oddStarOuterCircleProbability_map_rotation
