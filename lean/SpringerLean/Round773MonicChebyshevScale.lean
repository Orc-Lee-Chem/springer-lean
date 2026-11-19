import SpringerLean.Round772ChebyshevZeroDiscrepancy
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SpringerLean

open Polynomial

noncomputable def monicChebyshevScale (n : ℕ) : ℝ :=
  (2 : ℝ) ^ ((1 : ℝ) / n - 1)

noncomputable def monicChebyshevCandidate (n : ℕ) : ℝ[X] :=
  (Chebyshev.T ℝ (n : ℤ)).comp (C (monicChebyshevScale n) * X)

theorem monicChebyshevScale_factor (n : ℕ) (hn : 0 < n) :
    (2 : ℝ) ^ (n - 1) * (monicChebyshevScale n) ^ n = 1 := by
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnle : 1 ≤ n := hn
  rw [← Real.rpow_natCast, monicChebyshevScale,
    ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hexp : ((n - 1 : ℕ) : ℝ) + ((1 : ℝ) / n - 1) * n = 0 := by
    rw [Nat.cast_sub hnle]
    field_simp
    ring
  rw [hexp]
  simp

theorem monicChebyshevCandidate_monic (n : ℕ) (hn : 0 < n) :
    (monicChebyshevCandidate n).Monic := by
  rw [Monic, monicChebyshevCandidate]
  have hscale : monicChebyshevScale n ≠ 0 := by
    exact ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
  rw [leadingCoeff_comp (by simp [natDegree_C_mul_X _ hscale])]
  simp only [Chebyshev.leadingCoeff_T, Int.natAbs_natCast,
    Chebyshev.natDegree_T, leadingCoeff_C_mul_X]
  exact monicChebyshevScale_factor n hn

theorem monicChebyshevCandidate_roots (n : ℕ) :
    (monicChebyshevCandidate n).roots =
      (Chebyshev.T ℝ (n : ℤ)).roots.map
        (fun z => (monicChebyshevScale n)⁻¹ * z) := by
  have hscale : monicChebyshevScale n ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
  have hunit : IsUnit (monicChebyshevScale n) := isUnit_iff_ne_zero.mpr hscale
  unfold monicChebyshevCandidate
  conv_lhs => rw [← add_zero (C (monicChebyshevScale n) * X), ← C_0]
  simpa using roots_comp_C_mul_X_add_C (Chebyshev.T ℝ (n : ℤ))
    (monicChebyshevScale n) 0 hunit

end SpringerLean

#print axioms SpringerLean.monicChebyshevCandidate_monic
#print axioms SpringerLean.monicChebyshevCandidate_roots
