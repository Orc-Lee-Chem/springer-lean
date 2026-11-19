import SpringerLean.Round1724ActualPhaseGradientLocallyPowerBound

namespace SpringerLean

/-- The elementary power cancellation behind both singular-looking
R and S fluxes near a filling zero. -/
theorem phase_square_div_le_power
    (y U : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hy : 0 < y) (hU : |U| ≤ y^k) :
    U^2 / y ≤ y^(2 * k - 1) := by
  have hsq : U^2 ≤ (y^k)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg U) hU 2
    simpa only [sq_abs] using hh
  have hpow : (y^k)^2 = y^(2 * k - 1) * y := by
    rw [← pow_mul, ← pow_succ]
    congr 1
    omega
  rw [hpow] at hsq
  exact (div_le_iff₀ hy).mpr (by nlinarith)

end SpringerLean

#print axioms SpringerLean.phase_square_div_le_power
