import SpringerLean.Round2011OddStarMovingPointMembership

namespace SpringerLean

theorem oddStarOppositeTip_phase_pow_one
    (m : ℕ) (hm : 0 < m) (hodd : Odd m) :
    (Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) *
      Complex.I)) ^ m = 1 := by
  obtain ⟨k, hk⟩ := hodd
  have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hangle : (m : ℝ) * (Real.pi - Real.pi / (m : ℝ)) =
      (k : ℝ) * (2 * Real.pi) := by
    have hkeq : m = 2 * k + 1 := hk
    rw [hkeq]
    have hden : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  rw [← Complex.exp_nat_mul]
  have hcast : (m : ℂ) * (((Real.pi - Real.pi / (m : ℝ)) : ℝ) *
      Complex.I) = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    calc
      (m : ℂ) * (((Real.pi - Real.pi / (m : ℝ)) : ℝ) *
          Complex.I) =
          (((m : ℝ) * (Real.pi - Real.pi / (m : ℝ)) : ℝ) : ℂ) *
            Complex.I := by push_cast; ring
      _ = (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
        rw [hangle]
      _ = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast
        ring
  rw [hcast, Complex.exp_nat_mul_two_pi_mul_I]

theorem oddStarOppositeTip_mem_omitted
    (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m)
    (t : ℝ) (ht : |t| < 1) :
    (oddStarTipRadius m t : ℂ) *
        Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I) ∈
      oddStarPerturbationOmitted m t := by
  have hm0 : 0 < m := by omega
  have hbase : 0 ≤ 4 * Real.sqrt (1 - t ^ 2) := by positivity
  have hRpow : oddStarTipRadius m t ^ m =
      4 * Real.sqrt (1 - t ^ 2) := by
    simpa only [oddStarTipRadius] using
      Real.rpow_inv_natCast_pow hbase (by omega : m ≠ 0)
  have hRpowC : (oddStarTipRadius m t : ℂ) ^ m =
      ((4 * Real.sqrt (1 - t ^ 2) : ℝ) : ℂ) := by
    exact_mod_cast hRpow
  apply (oddStarPerturbation_omitted_tips m (by omega) t ht).2
  rw [mul_pow, oddStarOppositeTip_phase_pow_one m hm0 hodd,
    mul_one, hRpowC]

end SpringerLean
