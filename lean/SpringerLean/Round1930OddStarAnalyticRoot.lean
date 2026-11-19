import SpringerLean.Round1929OddStarReciprocal
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

namespace SpringerLean

noncomputable def oddStarSeedRootReciprocal
    (m : ℕ) (t : ℝ) (u : ℂ) : ℂ :=
  let s := Real.sqrt (1 - t ^ 2)
  (1 + ((s : ℂ) - (t : ℂ) * Complex.I) * u) ^
      ((2 : ℂ) / (m : ℂ)) *
    (1 - (t : ℂ) * Complex.I * u) ^
      (-((1 : ℂ) / (m : ℂ)))

theorem oddStarSeedRootReciprocal_zero (m : ℕ) (t : ℝ) :
    oddStarSeedRootReciprocal m t 0 = 1 := by
  simp [oddStarSeedRootReciprocal]

/-- The explicit analytic branch raises to the reciprocal seed. -/
theorem oddStarSeedRootReciprocal_pow
    (m : ℕ) (hm : 0 < m) (t : ℝ) (u : ℂ) :
    (oddStarSeedRootReciprocal m t u) ^ m =
      oddStarSeedReciprocal t u := by
  let a : ℂ := 1 +
    ((Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I) * u
  let b : ℂ := 1 - (t : ℂ) * Complex.I * u
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hnum : (a ^ ((2 : ℂ) / (m : ℂ))) ^ m = a ^ (2 : ℕ) := by
    rw [← Complex.cpow_nat_mul]
    have h : (m : ℂ) * ((2 : ℂ) / (m : ℂ)) = 2 := by
      field_simp [hm0]
    rw [h, Complex.cpow_two]
  have hden : (b ^ (-((1 : ℂ) / (m : ℂ)))) ^ m = b⁻¹ := by
    rw [← Complex.cpow_nat_mul]
    have h : (m : ℂ) * (-((1 : ℂ) / (m : ℂ))) = -1 := by
      field_simp [hm0]
    rw [h, Complex.cpow_neg_one]
  change (a ^ ((2 : ℂ) / (m : ℂ)) *
      b ^ (-((1 : ℂ) / (m : ℂ)))) ^ m = a ^ 2 / b
  rw [mul_pow, hnum, hden]
  exact (div_eq_mul_inv _ _).symm

/-- The explicit branch is holomorphic on the full open unit disk. -/
theorem oddStarSeedRootReciprocal_analyticOnNhd_unitDisk
    (m : ℕ) (t : ℝ) (ht : |t| < 1) :
    AnalyticOnNhd ℂ (oddStarSeedRootReciprocal m t)
      (Metric.ball (0 : ℂ) 1) := by
  change AnalyticOnNhd ℂ
    (fun u : ℂ =>
      (1 + ((Real.sqrt (1 - t ^ 2) : ℂ) -
        (t : ℂ) * Complex.I) * u) ^
          ((2 : ℂ) / (m : ℂ)) *
        (1 - (t : ℂ) * Complex.I * u) ^
          (-((1 : ℂ) / (m : ℂ))))
      (Metric.ball (0 : ℂ) 1)
  apply AnalyticOnNhd.mul
  · apply AnalyticOnNhd.cpow
    · fun_prop
    · fun_prop
    · intro u hu
      apply Complex.mem_slitPlane_iff.mpr
      left
      exact (oddStarSeed_reciprocal_factors_re_pos t ht u
        (by simpa [Metric.mem_ball, dist_zero_right] using hu)).1
  · apply AnalyticOnNhd.cpow
    · fun_prop
    · fun_prop
    · intro u hu
      apply Complex.mem_slitPlane_iff.mpr
      left
      exact (oddStarSeed_reciprocal_factors_re_pos t ht u
        (by simpa [Metric.mem_ball, dist_zero_right] using hu)).2

end SpringerLean

#print axioms SpringerLean.oddStarSeedRootReciprocal_pow
#print axioms SpringerLean.oddStarSeedRootReciprocal_analyticOnNhd_unitDisk
