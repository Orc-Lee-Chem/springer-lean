import SpringerLean.Round1972GeneralLemniscateNormalization
import Mathlib.Algebra.Polynomial.Derivative

open Polynomial

namespace SpringerLean

/-- Every derivative order obeys the affine chain rule for the
arbitrary complex-polynomial normalization used in 9.2. -/
theorem iterate_derivative_comp_affine_complex
    (P : ℂ[X]) (r c : ℂ) (j : ℕ) :
    (derivative^[j]) (P.comp (C r * X + C c)) =
      C (r ^ j) * (((derivative^[j]) P).comp (C r * X + C c)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, derivative_mul, derivative_C,
      zero_mul, zero_add, derivative_comp]
    rw [derivative_add, derivative_C_mul_X, derivative_C, add_zero]
    simp only [Function.iterate_succ_apply', pow_succ, map_mul]
    ring

theorem iterate_derivative_mul_C_complex
    (P : ℂ[X]) (a : ℂ) (j : ℕ) :
    (derivative^[j]) (P * C a) =
      ((derivative^[j]) P) * C a := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, derivative_mul, derivative_C]
    simp only [mul_zero, add_zero, Function.iterate_succ_apply']

/-- The full multiset of derivative zeros, with multiplicities,
transforms by the same affine map as the original zero multiset. -/
theorem polynomialAffineMonic_derivative_roots_map
    (P : ℂ[X]) (hP : 0 < P.natDegree)
    (c : ℂ) (r : ℝ) (hr : r ≠ 0) (j : ℕ) :
    (((derivative^[j]) (polynomialAffineMonic P c r)).roots.map
      (fun z : ℂ => (r : ℂ) * z + c)) =
        ((derivative^[j]) P).roots := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  let U : ℂ[X] := P.comp (C (r : ℂ) * X + C c)
  have hU : U ≠ 0 := by
    intro hzero
    have hQ := (polynomialAffineMonic_monic P hP c r hr).ne_zero
    apply hQ
    simp [polynomialAffineMonic, U, hzero]
  have hscalar : U.leadingCoeff⁻¹ ≠ 0 :=
    inv_ne_zero (leadingCoeff_ne_zero.mpr hU)
  have hcoef : (r : ℂ) ^ j * U.leadingCoeff⁻¹ ≠ 0 :=
    mul_ne_zero (pow_ne_zero j hrc) hscalar
  have hderiv : (derivative^[j]) (polynomialAffineMonic P c r) =
      C ((r : ℂ) ^ j * U.leadingCoeff⁻¹) *
        (((derivative^[j]) P).comp (C (r : ℂ) * X + C c)) := by
    unfold polynomialAffineMonic
    rw [iterate_derivative_mul_C_complex,
      iterate_derivative_comp_affine_complex]
    simp only [map_mul]
    ring
  rw [hderiv, roots_C_mul _ hcoef]
  exact map_roots_comp_C_mul_X_add_C ((derivative^[j]) P)
    (r : ℂ) c (isUnit_iff_ne_zero.mpr hrc)

end SpringerLean

#print axioms SpringerLean.iterate_derivative_comp_affine_complex
#print axioms SpringerLean.polynomialAffineMonic_derivative_roots_map
