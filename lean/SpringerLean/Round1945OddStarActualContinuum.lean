import SpringerLean.Round1944OddStarOmittedConnected

namespace SpringerLean

/-- For every admissible perturbation parameter, the explicitly
constructed omitted set is an actual compact connected nondegenerate
plane set, and it retains the prescribed rotational symmetry. -/
theorem oddStarPerturbation_actual_continuum
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    IsCompact (oddStarPerturbationOmitted m t) ∧
    IsConnected (oddStarPerturbationOmitted m t) ∧
    (∃ x y : ℂ,
      x ∈ oddStarPerturbationOmitted m t ∧
      y ∈ oddStarPerturbationOmitted m t ∧ x ≠ y) ∧
    (∀ η w : ℂ, η ^ m = 1 →
      (η * w ∈ oddStarPerturbationOmitted m t ↔
        w ∈ oddStarPerturbationOmitted m t)) := by
  refine ⟨oddStarPerturbation_omitted_isCompact m hm t ht,
    oddStarPerturbation_omitted_connected m hm t ht, ?_,
    oddStarPerturbation_omitted_rotation_iff m hm t ht⟩
  let s : ℝ := Real.sqrt (1 - t ^ 2)
  have hspos : 0 < s := oddStarSeed_sqrt_pos t ht
  have htarget : ((4 * s : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hspos.ne')
  obtain ⟨w, hw⟩ :=
    IsAlgClosed.exists_pow_nat_eq ((4 * s : ℝ) : ℂ) (by omega : 0 < m)
  have hw0 : w ≠ 0 := by
    intro hzero
    rw [hzero] at hw
    simp [zero_pow (by omega : m ≠ 0)] at hw
    exact hspos.ne' hw
  refine ⟨0, w, (oddStarPerturbation_omitted_tips m hm t ht).1,
    (oddStarPerturbation_omitted_tips m hm t ht).2 w ?_, ?_⟩
  · simpa [s] using hw
  · exact Ne.symm hw0

end SpringerLean

#print axioms SpringerLean.oddStarPerturbation_actual_continuum
