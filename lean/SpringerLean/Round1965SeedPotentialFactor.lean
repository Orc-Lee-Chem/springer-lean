import SpringerLean.Round1964OddBoundaryProbability

namespace SpringerLean

/-- The second algebraic preimage of the rational seed, paired with
`z` under `oddStarSeed t`. -/
noncomputable def oddStarSeedPartner (t : ℝ) (z : ℂ) : ℂ :=
  (1 + (t : ℂ) * Complex.I * z) /
    (z - (t : ℂ) * Complex.I)

/-- Exact factorization needed to compute the logarithmic potential of
the seed's angular boundary law by circle averaging. -/
theorem oddStarSeed_difference_factor
    (t : ℝ) (ht : |t| < 1) (z u : ℂ)
    (hz : z - (t : ℂ) * Complex.I ≠ 0)
    (hu : u - (t : ℂ) * Complex.I ≠ 0) :
    oddStarSeed t u - oddStarSeed t z =
      (u - z) * (u - oddStarSeedPartner t z) /
        (u - (t : ℂ) * Complex.I) := by
  have hnonneg : 0 ≤ 1 - t ^ 2 := by
    rcases abs_lt.mp ht with ⟨hlo, hhi⟩
    nlinarith
  have hs2 : (Real.sqrt (1 - t ^ 2) : ℂ) ^ 2 = (1 - t ^ 2 : ℝ) := by
    exact_mod_cast Real.sq_sqrt hnonneg
  unfold oddStarSeed oddStarSeedPartner
  field_simp [hz, hu]
  push_cast at hs2
  have hbr : ((t : ℂ) * Complex.I) ^ 2 -
      (Real.sqrt (1 - t ^ 2) : ℂ) ^ 2 + 1 = 0 := by
    rw [hs2]
    simp only [mul_pow, Complex.I_sq]
    ring
  linear_combination (u - z) * hbr

/-- For an exterior point, the other algebraic preimage lies strictly
inside the unit disk. -/
theorem oddStarSeedPartner_norm_lt_one
    (t : ℝ) (ht : |t| < 1) (z : ℂ) (hz : 1 < ‖z‖) :
    ‖oddStarSeedPartner t z‖ < 1 := by
  have hden : z - (t : ℂ) * Complex.I ≠ 0 := by
    intro hzero
    have hz' : z = (t : ℂ) * Complex.I := sub_eq_zero.mp hzero
    have hn : ‖z‖ = |t| := by
      rw [hz', norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
      rfl
    rw [hn] at hz
    linarith
  have hq : 0 < 1 - t ^ 2 := by
    rcases abs_lt.mp ht with ⟨hlo, hhi⟩
    nlinarith
  have hz2 : 0 < ‖z‖ ^ 2 - 1 := by
    nlinarith [norm_nonneg z]
  have hdiff := oddStarSeed_partner_norm_identity t z
  have hnum : ‖1 + (t : ℂ) * Complex.I * z‖ <
      ‖z - (t : ℂ) * Complex.I‖ := by
    nlinarith [mul_pos hq hz2,
      norm_nonneg (1 + (t : ℂ) * Complex.I * z),
      norm_nonneg (z - (t : ℂ) * Complex.I)]
  unfold oddStarSeedPartner
  rw [norm_div]
  exact (div_lt_one (norm_pos_iff.mpr hden)).mpr hnum

end SpringerLean

#print axioms SpringerLean.oddStarSeed_difference_factor
#print axioms SpringerLean.oddStarSeedPartner_norm_lt_one
