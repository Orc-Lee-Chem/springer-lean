import SpringerLean.Round1934OddStarCenteredGerm

namespace SpringerLean

/-- The odd-star construction is an actual centered exterior map,
with the rotational and power-map identities needed for the continuum. -/
theorem oddStarPerturbation_actual_exterior_map
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    CenteredExteriorUnivalent (oddStarPerturbation m t) ∧
      (∀ η z : ℂ, η ^ m = 1 →
        oddStarPerturbation m t (η * z) =
          η * oddStarPerturbation m t z) ∧
      (∀ z ∈ exteriorDisk,
        (oddStarPerturbation m t z) ^ m = oddStarSeed t (z ^ m)) := by
  refine ⟨oddStarPerturbation_centeredExteriorUnivalent m hm t ht,
    ?_, ?_⟩
  · exact fun η z hη => oddStarPerturbation_rotation m t η z hη
  · exact fun z hz => oddStarPerturbation_pow_eq_seed m (by omega) t ht z hz

/-- The unperturbed map is the standard regular-star exterior map. -/
theorem oddStarPerturbation_zero_formula
    (m : ℕ) (z : ℂ) :
    oddStarPerturbation m 0 z =
      z * (1 + (z ^ m)⁻¹) ^ ((2 : ℂ) / (m : ℂ)) := by
  simp [oddStarPerturbation, oddStarSeedRootReciprocal]

end SpringerLean

#print axioms SpringerLean.oddStarPerturbation_actual_exterior_map
#print axioms SpringerLean.oddStarPerturbation_zero_formula
