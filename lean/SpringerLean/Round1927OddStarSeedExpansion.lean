import SpringerLean.Round1926OddStarSeedTips

namespace SpringerLean

/-- The odd-star seed is a translated slit map with a shifted pole.
Its leading Laurent coefficient at infinity is one. -/
theorem oddStarSeed_expansion (t : ℝ) (z : ℂ)
    (hz : z - (t : ℂ) * Complex.I ≠ 0) :
    oddStarSeed t z =
      (z - (t : ℂ) * Complex.I) +
        2 * (Real.sqrt (1 - t ^ 2) : ℂ) +
        (Real.sqrt (1 - t ^ 2) : ℂ) ^ 2 /
          (z - (t : ℂ) * Complex.I) := by
  unfold oddStarSeed
  field_simp [hz]
  ring

/-- At the unperturbed parameter the seed is the shifted Joukowski map. -/
theorem oddStarSeed_zero_expansion (z : ℂ) (hz : z ≠ 0) :
    oddStarSeed 0 z = z + 2 + z⁻¹ := by
  have h := oddStarSeed_expansion 0 z (by simpa using hz)
  norm_num at h
  rw [h]

end SpringerLean

#print axioms SpringerLean.oddStarSeed_expansion
#print axioms SpringerLean.oddStarSeed_zero_expansion
