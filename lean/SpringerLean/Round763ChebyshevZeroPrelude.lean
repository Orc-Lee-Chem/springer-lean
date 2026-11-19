import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

namespace SpringerLean

open Polynomial

/-- The first derivative of a real Chebyshev polynomial has exactly the
second-kind Chebyshev zeros. This is the first zero-comparison input for
Proposition 9.2; higher derivatives and the empirical limit remain open. -/
theorem chebyshev_first_derivative_roots (n : ℕ) (hn : 0 < n) :
    (derivative (Chebyshev.T ℝ (n : ℤ))).roots =
      ((Finset.range (n - 1)).image
        (fun k : ℕ => Real.cos ((k + 1) * Real.pi / n))).val := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hcast : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
  rw [Chebyshev.T_derivative_eq_U, hcast]
  change (C (n : ℝ) * Chebyshev.U ℝ ((n - 1 : ℕ) : ℤ)).roots = _
  rw [roots_C_mul _ hn0, Chebyshev.roots_U_real]
  ext k
  congr 1
  simp [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))]

end SpringerLean

#print axioms SpringerLean.chebyshev_first_derivative_roots
