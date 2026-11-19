import SpringerLean.Round774ChebyshevScaleLimit

open Polynomial

namespace SpringerLean

/-- All derivative orders retain the exact linear scaling. -/
theorem iterate_derivative_comp_C_mul_X_real (P : ℝ[X]) (s : ℝ) (j : ℕ) :
    (derivative^[j]) (P.comp (C s * X)) =
      C (s ^ j) * (((derivative^[j]) P).comp (C s * X)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, derivative_mul, derivative_C,
      zero_mul, zero_add, derivative_comp]
    simp only [derivative_mul, derivative_C, derivative_X, zero_mul, zero_add, mul_one]
    simp only [Function.iterate_succ_apply', pow_succ, map_mul]
    ring

/-- Exact root multiset under linear scaling; the scalar factor from
the chain rule is nonzero and hence introduces no roots. -/
theorem roots_iterate_derivative_comp_C_mul_X_real
    (P : ℝ[X]) (s : ℝ) (hs : s ≠ 0) (j : ℕ) :
    (((derivative^[j]) (P.comp (C s * X))).roots) =
      (((derivative^[j]) P).roots).map (fun x => s⁻¹ * x) := by
  rw [iterate_derivative_comp_C_mul_X_real, roots_C_mul _ (pow_ne_zero j hs)]
  conv_lhs => rw [← add_zero (C s * X), ← C_0]
  simpa using roots_comp_C_mul_X_add_C ((derivative^[j]) P) s 0
    (isUnit_iff_ne_zero.mpr hs)

theorem monicChebyshevCandidate_derivative_roots (n j : ℕ) :
    (((derivative^[j]) (monicChebyshevCandidate n)).roots) =
      (((derivative^[j]) (Chebyshev.T ℝ (n : ℤ))).roots).map
        (fun x => (monicChebyshevScale n)⁻¹ * x) := by
  exact roots_iterate_derivative_comp_C_mul_X_real _ _
    (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)) j

theorem monicChebyshevScale_inv_le_two (n : ℕ) :
    (monicChebyshevScale n)⁻¹ ≤ (2 : ℝ) := by
  have hhalf : (1 / 2 : ℝ) ≤ monicChebyshevScale n := by
    have hexp : (-1 : ℝ) ≤ 1 / (n : ℝ) - 1 := by
      have hh : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      linarith
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
    change (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 / (n : ℝ) - 1)
    calc
      (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (1 / (n : ℝ) - 1) := hh
  calc
    _ = 1 / monicChebyshevScale n := (one_div _).symm
    _ ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hhalf
    _ = 2 := by norm_num

end SpringerLean

#print axioms SpringerLean.monicChebyshevCandidate_derivative_roots
#print axioms SpringerLean.monicChebyshevScale_inv_le_two
