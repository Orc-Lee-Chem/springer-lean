import SpringerLean.Round1970PolynomialLemniscateNormalization
import Mathlib.Algebra.Polynomial.Roots

open Polynomial

namespace SpringerLean

/-- The zero centroid, with roots counted by multiplicity. -/
noncomputable def polynomialZeroCentroid (P : ℂ[X]) : ℂ :=
  P.roots.sum / (P.natDegree : ℂ)

/-- The affine monic normalization carries its multiplicity-counted
zeros to the original zeros by the same affine map. -/
theorem polynomialAffineMonic_roots_map
    (P : ℂ[X]) (hP : 0 < P.natDegree)
    (c : ℂ) (r : ℝ) (hr : r ≠ 0) :
    ((polynomialAffineMonic P c r).roots.map
      (fun z : ℂ => (r : ℂ) * z + c)) = P.roots := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  let U : ℂ[X] := P.comp (C (r : ℂ) * X + C c)
  have hU : U ≠ 0 := by
    intro hzero
    have hQ := (polynomialAffineMonic_monic P hP c r hr).ne_zero
    apply hQ
    simp [polynomialAffineMonic, U, hzero]
  have hscalar : U.leadingCoeff⁻¹ ≠ 0 :=
    inv_ne_zero (leadingCoeff_ne_zero.mpr hU)
  have hroots : (polynomialAffineMonic P c r).roots = U.roots := by
    change (U * C U.leadingCoeff⁻¹).roots = U.roots
    rw [mul_comm, roots_C_mul U hscalar]
  rw [hroots]
  exact map_roots_comp_C_mul_X_add_C P (r : ℂ) c
    (isUnit_iff_ne_zero.mpr hrc)

private theorem multiset_sum_affine
    (s : Multiset ℂ) (a b : ℂ) :
    (s.map (fun z => a * z + b)).sum =
      a * s.sum + (s.card : ℂ) * b := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
        Nat.cast_add, Nat.cast_one]
      rw [ih]
      ring

/-- Choosing the translation point as the multiplicity-counted zero
centroid makes the normalized polynomial centered. -/
theorem polynomialAffineMonic_roots_sum_eq_zero
    (P : ℂ[X]) (hP : 0 < P.natDegree)
    (r : ℝ) (hr : r ≠ 0) :
    (polynomialAffineMonic P (polynomialZeroCentroid P) r).roots.sum = 0 := by
  let Q := polynomialAffineMonic P (polynomialZeroCentroid P) r
  let c := polynomialZeroCentroid P
  have hcard : Q.roots.card = P.natDegree := by
    have hsplit := (IsAlgClosed.splits Q).natDegree_eq_card_roots
    rw [polynomialAffineMonic_natDegree P c r hr] at hsplit
    exact hsplit.symm
  have hsum := congrArg Multiset.sum
    (polynomialAffineMonic_roots_map P hP c r hr)
  rw [multiset_sum_affine, hcard] at hsum
  have hn : (P.natDegree : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hP
  have hcent : (P.natDegree : ℂ) * c = P.roots.sum := by
    dsimp [c, polynomialZeroCentroid]
    field_simp [hn]
  have hm : (r : ℂ) * Q.roots.sum = 0 := by
    linear_combination hsum - hcent
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  exact (mul_eq_zero.mp hm).resolve_left hrc

end SpringerLean

#print axioms SpringerLean.polynomialAffineMonic_roots_map
#print axioms SpringerLean.polynomialAffineMonic_roots_sum_eq_zero
