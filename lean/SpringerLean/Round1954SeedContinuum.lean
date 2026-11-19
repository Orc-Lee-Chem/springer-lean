import SpringerLean.Round1953FactorScaling

namespace SpringerLean

/-- The seed omitted set is a compact, connected, nondegenerate
continuum for every parameter used in the odd-star deformation. -/
theorem oddStarSeed_actual_continuum
    (t : ℝ) (ht : |t| < 1) :
    IsCompact (oddStarSeedOmitted t) ∧
    IsConnected (oddStarSeedOmitted t) ∧
    (∃ x y : ℂ,
      x ∈ oddStarSeedOmitted t ∧
      y ∈ oddStarSeedOmitted t ∧ x ≠ y) := by
  have hcompact : IsCompact (oddStarSeedOmitted t) := by
    rw [oddStarSeed_omitted_eq_boundary_image t ht]
    exact (isCompact_sphere (0 : ℂ) 1).image_of_continuousOn
      (oddStarSeed_continuousOn_circle t ht)
  refine ⟨hcompact, oddStarSeed_omitted_connected t ht, ?_⟩
  let s : ℝ := Real.sqrt (1 - t ^ 2)
  have hspos : 0 < s := oddStarSeed_sqrt_pos t ht
  have hnonzero : ((4 * s : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hspos.ne')
  refine ⟨0, ((4 * s : ℝ) : ℂ),
    oddStarSeed_zero_mem_omitted t ht, ?_, hnonzero.symm⟩
  simpa [s] using oddStarSeed_four_s_mem_omitted t ht

end SpringerLean

#print axioms SpringerLean.oddStarSeed_actual_continuum
