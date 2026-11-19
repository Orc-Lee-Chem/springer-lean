import SpringerLean.Round1995OddStarRootRotation

open MeasureTheory Set

namespace SpringerLean

private theorem log_distance_integral_of_rotation
    (ν : Measure ℂ) (η w : ℂ) (hηnorm : ‖η‖ = 1)
    (hmap : ν.map (fun u : ℂ => η * u) = ν) :
    (∫ u, Real.log ‖u - η * w‖ ∂ν) =
      ∫ u, Real.log ‖u - w‖ ∂ν := by
  have hrot : AEMeasurable (fun u : ℂ => η * u) ν := by fun_prop
  have hlog : AEStronglyMeasurable
      (fun u : ℂ => Real.log ‖u - η * w‖)
      (ν.map (fun u : ℂ => η * u)) := by
    exact (Real.measurable_log.comp
      (measurable_norm.comp (measurable_id.sub measurable_const))).aestronglyMeasurable
  calc
    (∫ u, Real.log ‖u - η * w‖ ∂ν) =
        ∫ u, Real.log ‖u - η * w‖
          ∂(ν.map (fun u : ℂ => η * u)) := by rw [hmap]
    _ = ∫ u, Real.log ‖η * u - η * w‖ ∂ν :=
      integral_map hrot hlog
    _ = ∫ u, Real.log ‖u - w‖ ∂ν := by
      apply integral_congr_ae
      filter_upwards with u
      rw [← mul_sub, norm_mul, hηnorm, one_mul]

/-- The cyclic logarithmic potential of the actual odd-star radial law
is m times its ordinary logarithmic potential at every point outside
the actual omitted continuum. -/
theorem oddStarActualBoundaryProbability_cyclic_log_integral
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    (w : ℂ) (hw : w ∉ oddStarPerturbationOmitted m t) :
    (∫ u, Real.log ‖u ^ m - w ^ m‖
      ∂oddStarActualBoundaryProbability m t) =
        (m : ℝ) *
          (∫ u, Real.log ‖u - w‖
            ∂oddStarActualBoundaryProbability m t) := by
  let ν : Measure ℂ := oddStarActualBoundaryProbability m t
  let K : Set ℂ := oddStarPerturbationOmitted m t
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))
  have hmpos : 0 < m := by omega
  have hζ : IsPrimitiveRoot ζ m :=
    Complex.isPrimitiveRoot_exp m (Nat.ne_of_gt hmpos)
  have hwE : w ^ m ∉ oddStarSeedOmitted t := by
    intro h
    apply hw
    rw [oddStarPerturbation_omitted_eq_power_preimage m hm t ht]
    exact h
  have hpowae : ∀ᵐ u ∂ν, u ^ m ≠ w ^ m := by
    filter_upwards [oddStarPerturbation_actual_boundary_probability_ae_omitted
      m hm t ht] with u hu
    intro heq
    apply hwE
    have huE : u ^ m ∈ oddStarSeedOmitted t := by
      rw [oddStarPerturbation_omitted_eq_power_preimage m hm t ht] at hu
      exact hu
    rwa [heq] at huE
  have hroot (j : ℕ) : (ζ ^ j) ^ m = 1 := by
    rw [← pow_mul, mul_comm j m, pow_mul, hζ.pow_eq_one, one_pow]
  have hrootnorm (j : ℕ) : ‖ζ ^ j‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (hroot j) (by omega)
  have hwrot (j : ℕ) : ζ ^ j * w ∉ K := by
    intro hK
    have hpowK : (ζ ^ j * w) ^ m ∈ oddStarSeedOmitted t := by
      change ζ ^ j * w ∈ oddStarPerturbationOmitted m t at hK
      rw [oddStarPerturbation_omitted_eq_power_preimage m hm t ht] at hK
      exact hK
    rw [mul_pow, hroot j, one_mul] at hpowK
    exact hwE hpowK
  haveI : IsFiniteMeasure ν :=
    Measure.isFiniteMeasure_map oddStarAngularProbability _
  have hterm (j : ℕ) : Integrable
      (fun u : ℂ => Real.log ‖u - ζ ^ j * w‖) ν :=
    oddStarActualBoundaryProbability_log_distance_integrable
      m hm t ht (ζ ^ j * w) (hwrot j)
  have hpoint : ∀ᵐ u ∂ν,
      Real.log ‖u ^ m - w ^ m‖ =
        ∑ j ∈ Finset.range m, Real.log ‖u - ζ ^ j * w‖ := by
    filter_upwards [hpowae] with u hu
    simpa [Finset.sum_eq_multiset_sum, ζ] using
      cyclic_power_difference_log_sum m hmpos u w hu
  calc
    (∫ u, Real.log ‖u ^ m - w ^ m‖ ∂ν) =
        ∫ u, ∑ j ∈ Finset.range m,
          Real.log ‖u - ζ ^ j * w‖ ∂ν := integral_congr_ae hpoint
    _ = ∑ j ∈ Finset.range m,
          ∫ u, Real.log ‖u - ζ ^ j * w‖ ∂ν := by
            exact integral_finsetSum (Finset.range m)
              (fun j _ => hterm j)
    _ = ∑ j ∈ Finset.range m,
          ∫ u, Real.log ‖u - w‖ ∂ν := by
            apply Finset.sum_congr rfl
            intro j _
            exact log_distance_integral_of_rotation ν (ζ ^ j) w
              (hrootnorm j)
              (oddStarActualBoundaryProbability_map_root_rotation
                m hm t ht (ζ ^ j) (hroot j))
    _ = (m : ℝ) * (∫ u, Real.log ‖u - w‖ ∂ν) := by simp

/-- The ordinary logarithmic potential of the actual odd-star radial
boundary probability is the Green function of its actual exterior
coordinate at every point outside the actual omitted continuum. -/
theorem oddStarActualBoundaryProbability_log_potential_outside_star
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    (w : ℂ) (hw : w ∉ oddStarPerturbationOmitted m t) :
    ∃ z : ℂ, z ∈ exteriorDisk ∧ oddStarPerturbation m t z = w ∧
      (∫ u, Real.log ‖u - w‖
        ∂oddStarActualBoundaryProbability m t) = Real.log ‖z‖ := by
  obtain ⟨z, hz, hzw, hpower⟩ :=
    oddStarActualBoundaryProbability_power_log_potential_outside_star
      m hm t ht w hw
  have hcyc := oddStarActualBoundaryProbability_cyclic_log_integral
    m hm t ht w hw
  refine ⟨z, hz, hzw, ?_⟩
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  exact mul_left_cancel₀ hmne (hcyc.symm.trans hpower)

end SpringerLean

#print axioms SpringerLean.oddStarActualBoundaryProbability_cyclic_log_integral
#print axioms SpringerLean.oddStarActualBoundaryProbability_log_potential_outside_star
