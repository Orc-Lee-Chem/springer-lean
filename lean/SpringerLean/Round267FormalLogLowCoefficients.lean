import SpringerLean.Round266FiniteFormalLog
import SpringerLean.Round265AllFiniteGrunsky
import SpringerLean.Round184BivariateSymmetry

namespace SpringerLean
open PowerSeries

theorem formalNegativeLogSeries_coeff_inner (k : ℕ) :
    PowerSeries.coeff k (formalNegativeLogSeries (PowerSeries ℂ)) =
      PowerSeries.C (PowerSeries.coeff k (formalNegativeLogSeries ℂ)) := by
  have h := congrArg (PowerSeries.coeff k)
    (formalNegativeLogSeries_map (PowerSeries.C : ℂ →+* PowerSeries ℂ))
  simpa only [PowerSeries.coeff_map] using h.symm

/-- Equality of a finite reciprocal coefficient square is preserved by
the normalized logarithm. Discarded powers have proved zero coefficients. -/
theorem schoberLowEq_negative_log
    {n : ℕ} {A B : PowerSeries (PowerSeries ℂ)}
    (hA : PowerSeries.constantCoeff A = 0)
    (hB : PowerSeries.constantCoeff B = 0)
    (hAB : schoberLowEq n A B) :
    schoberLowEq n (-PowerSeries.logOf (1 - A))
      (-PowerSeries.logOf (1 - B)) := by
  intro i j hi hj
  unfold schoberBiCoeff
  rw [formal_negative_log_coeff_finite A hA j n (by omega),
    formal_negative_log_coeff_finite B hB j n (by omega)]
  simp only [map_sum, formalNegativeLogSeries_coeff_inner,
    PowerSeries.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact schoberLowEq_pow hAB k i j hi hj

theorem formalFaberKernel_low_symm (f : PowerSeries ℂ) (n : ℕ) :
    schoberLowSymm n (formalFaberKernel f) := by
  intro i j hi hj
  cases i with
  | zero =>
      cases j with
      | zero => rfl
      | succ j => simp [schoberBiCoeff, PowerSeries.coeff_zero_eq_constantCoeff]
  | succ i =>
      cases j with
      | zero => simp [schoberBiCoeff, PowerSeries.coeff_zero_eq_constantCoeff]
      | succ j =>
          simp [schoberBiCoeff, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem schoberLowSymm_negative_log
    {n : ℕ} {A : PowerSeries (PowerSeries ℂ)}
    (hA : PowerSeries.constantCoeff A = 0)
    (hSymm : schoberLowSymm n A) :
    schoberLowSymm n (-PowerSeries.logOf (1 - A)) := by
  have h1 : schoberLowSymm n (1 : PowerSeries (PowerSeries ℂ)) := by
    intro i j hi hj
    simp [schoberBiCoeff, PowerSeries.coeff_one]
    split_ifs <;> simp_all
  have hp (k : ℕ) : schoberLowSymm n (A ^ k) := by
    induction k with
    | zero => simpa using h1
    | succ k ih => simpa only [pow_succ] using schoberLowSymm_mul ih hSymm
  intro i j hi hj
  unfold schoberBiCoeff
  rw [formal_negative_log_coeff_finite A hA j n (by omega),
    formal_negative_log_coeff_finite A hA i n (by omega)]
  simp only [map_sum, formalNegativeLogSeries_coeff_inner,
    PowerSeries.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact hp k i j hi hj

theorem exteriorFormalGrunskyKernel_coeff_symm (F : ℂ → ℂ) (i j : ℕ) :
    PowerSeries.coeff i (PowerSeries.coeff j (exteriorFormalGrunskyKernel F)) =
      PowerSeries.coeff j (PowerSeries.coeff i (exteriorFormalGrunskyKernel F)) := by
  have h := schoberLowSymm_negative_log
    (n := max i j + 1)
    (show PowerSeries.constantCoeff (formalFaberKernel (exteriorFormalForward F)) = 0 by simp)
    (formalFaberKernel_low_symm (exteriorFormalForward F) (max i j + 1))
  exact h i j (by omega) (by omega)

end SpringerLean
