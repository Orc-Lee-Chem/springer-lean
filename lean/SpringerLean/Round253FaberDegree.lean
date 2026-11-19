import SpringerLean.Round252FaberRecurrence
import Mathlib.Algebra.Polynomial.BigOperators

namespace SpringerLean
open PowerSeries

theorem generalFaberGeneratorCorrection_coeff_natDegree_le
    {A : Type*} [CommRing A] (f : PowerSeries A) (n : ℕ) :
    (PowerSeries.coeff n (generalFaberGeneratorCorrection f)).natDegree ≤ n := by
  cases n with
  | zero =>
      simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n =>
      rw [generalFaberGeneratorCorrection_coeff_succ]
      by_cases hn : n = 0
      · subst n
        simpa using
          (Polynomial.natDegree_sub_le_of_le
            (Polynomial.natDegree_X_le : (Polynomial.X : Polynomial A).natDegree ≤ 1)
            (show (Polynomial.C (PowerSeries.coeff 0 f)).natDegree ≤ 1 by simp))
      · simp [hn]

/-- Every uniformly generated Faber polynomial has the claimed finite
degree. This makes its reciprocal analytic factor an actual finite sum. -/
theorem generalFaberPolynomial_natDegree_le
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (f : PowerSeries A) (n : ℕ) :
    (generalFaberPolynomial f n).natDegree ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [generalFaberPolynomial]
      | succ n =>
          rw [generalFaberPolynomial_antidiagonal_recurrence]
          apply Polynomial.natDegree_add_le_of_degree_le
          · calc
              _ ≤ ((n + 1 : ℕ) : Polynomial A).natDegree +
                  (PowerSeries.coeff (n + 1)
                    (generalFaberGeneratorCorrection f)).natDegree :=
                Polynomial.natDegree_mul_le
              _ ≤ 0 + (n + 1) := add_le_add (by simp)
                (generalFaberGeneratorCorrection_coeff_natDegree_le f (n + 1))
              _ = _ := by omega
          · apply Polynomial.natDegree_sum_le_of_forall_le
            intro ij hij
            have hijsum := Finset.mem_antidiagonal.mp hij
            by_cases hj : ij.2 = 0
            · simp [hj, PowerSeries.coeff_zero_eq_constantCoeff]
            · have hi : ij.1 + 1 < n + 1 := by omega
              calc
                _ ≤ (generalFaberPolynomial f (ij.1 + 1)).natDegree +
                    (PowerSeries.coeff ij.2
                      (generalFaberGeneratorCorrection f)).natDegree :=
                  Polynomial.natDegree_mul_le
                _ ≤ (ij.1 + 1) + ij.2 :=
                  add_le_add (ih (ij.1 + 1) hi)
                    (generalFaberGeneratorCorrection_coeff_natDegree_le f ij.2)
                _ = n + 1 := by omega

end SpringerLean
