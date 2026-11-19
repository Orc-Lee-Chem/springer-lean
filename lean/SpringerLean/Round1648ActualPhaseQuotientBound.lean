import SpringerLean.Round1647ActualModulusGradientNorm

namespace SpringerLean

/-- The actual phase quotient is bounded by |H|^(k-1), a necessary
factor when transferring the zero-safe weighted derivative estimate. -/
theorem actualHarmonicPhase_quotient_abs_le
    (F : ℂ → ℂ) (k : ℕ) (hk : 1 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1)
    (z : ℂ) (hH : actualHarmonic F z ≠ 0) :
    |actualHarmonicPhaseField F k beta z /
      ‖actualHarmonic F z‖| ≤
      ‖actualHarmonic F z‖^(k-1) := by
  let H := actualHarmonic F z
  let U := actualHarmonicPhaseField F k beta z
  have hUp : |U| ≤ ‖H‖^k := by
    calc
      |U| ≤ ‖beta*H^k‖ := Complex.abs_im_le_norm _
      _ = ‖H‖^k := by rw [norm_mul,hbeta,one_mul,norm_pow]
  have hpow : ‖H‖^k = ‖H‖*‖H‖^(k-1) := by
    conv_lhs => rw [show k=k-1+1 by omega,pow_succ]
    ring
  have hy : 0 < ‖H‖ := norm_pos_iff.mpr hH
  rw [abs_div, abs_of_nonneg (norm_nonneg H)]
  apply (div_le_iff₀ hy).mpr
  rw [hpow] at hUp
  simpa only [mul_comm] using hUp

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_quotient_abs_le
