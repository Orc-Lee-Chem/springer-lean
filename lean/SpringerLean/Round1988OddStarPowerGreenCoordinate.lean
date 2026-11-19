import SpringerLean.Round1987OddStarPowerPotential

open MeasureTheory Set

namespace SpringerLean

/-- At each actual exterior image point of an odd-star perturbation,
the logarithmic potential after taking the m-th power is exactly the
Green coordinate m log|z| of that same exterior map. -/
theorem oddStarActualBoundaryProbability_power_log_potential_exterior
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    (z : ℂ) (hz : z ∈ exteriorDisk) :
    (∫ u, Real.log ‖u ^ m - (oddStarPerturbation m t z) ^ m‖
      ∂oddStarActualBoundaryProbability m t) =
        (m : ℝ) * Real.log ‖z‖ := by
  have hm0 : m ≠ 0 := by omega
  have hzm : z ^ m ∈ exteriorDisk := by
    change 1 < ‖z ^ m‖
    rw [norm_pow]
    exact one_lt_pow₀ hz hm0
  have hpower := oddStarPerturbation_pow_eq_seed m (by omega) t ht z hz
  have hw : oddStarSeed t (z ^ m) ∉ oddStarSeedOmitted t := by
    change oddStarSeed t (z ^ m) ∉
      (oddStarSeed t '' exteriorDisk)ᶜ
    simp only [mem_compl_iff, not_not]
    exact ⟨z ^ m, hzm, rfl⟩
  obtain ⟨ζ, hζ, hζw, hpot⟩ :=
    oddStarActualBoundaryProbability_power_log_potential_outside
      m hm t ht (oddStarSeed t (z ^ m)) hw
  have hζeq : ζ = z ^ m :=
    oddStarSeed_injOn_exteriorDisk t ht hζ hzm hζw
  rw [hζeq] at hpot
  calc
    (∫ u, Real.log ‖u ^ m - (oddStarPerturbation m t z) ^ m‖
      ∂oddStarActualBoundaryProbability m t) =
        ∫ u, Real.log ‖u ^ m - oddStarSeed t (z ^ m)‖
          ∂oddStarActualBoundaryProbability m t := by rw [hpower]
    _ = Real.log ‖z ^ m‖ := hpot
    _ = (m : ℝ) * Real.log ‖z‖ := by rw [norm_pow, Real.log_pow]

/-- The same identity quantified over every point outside the actual
odd-star omitted continuum. -/
theorem oddStarActualBoundaryProbability_power_log_potential_outside_star
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    (w : ℂ) (hw : w ∉ oddStarPerturbationOmitted m t) :
    ∃ z : ℂ, z ∈ exteriorDisk ∧ oddStarPerturbation m t z = w ∧
      (∫ u, Real.log ‖u ^ m - w ^ m‖
        ∂oddStarActualBoundaryProbability m t) =
          (m : ℝ) * Real.log ‖z‖ := by
  have hmem : w ∈ oddStarPerturbation m t '' exteriorDisk := by
    simpa only [oddStarPerturbationOmitted, mem_compl_iff, not_not] using hw
  rcases hmem with ⟨z, hz, rfl⟩
  exact ⟨z, hz, rfl,
    oddStarActualBoundaryProbability_power_log_potential_exterior
      m hm t ht z hz⟩

end SpringerLean

#print axioms SpringerLean.oddStarActualBoundaryProbability_power_log_potential_exterior
#print axioms SpringerLean.oddStarActualBoundaryProbability_power_log_potential_outside_star
