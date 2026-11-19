import SpringerLean.Round1968PolynomialLemniscateInterior
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

open Polynomial

namespace SpringerLean

/-- Affine domain normalization followed by division by the resulting
leading coefficient. The center and radius can be selected later from
the original polynomial lemniscate. -/
noncomputable def polynomialAffineMonic
    (P : ℂ[X]) (c : ℂ) (r : ℝ) : ℂ[X] :=
  let U := P.comp (C (r : ℂ) * X + C c)
  U * C (U.leadingCoeff⁻¹)

theorem polynomialAffineMonic_natDegree
    (P : ℂ[X]) (c : ℂ) (r : ℝ) (hr : r ≠ 0) :
    (polynomialAffineMonic P c r).natDegree = P.natDegree := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hlinear : (C (r : ℂ) * X + C c : ℂ[X]).natDegree = 1 :=
    natDegree_linear hrc
  unfold polynomialAffineMonic
  rw [natDegree_mul_leadingCoeff_self_inv, natDegree_comp, hlinear]
  omega

theorem polynomialAffineMonic_monic
    (P : ℂ[X]) (hP : 0 < P.natDegree)
    (c : ℂ) (r : ℝ) (hr : r ≠ 0) :
    (polynomialAffineMonic P c r).Monic := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hlinear : (C (r : ℂ) * X + C c : ℂ[X]).natDegree = 1 :=
    natDegree_linear hrc
  have hU : P.comp (C (r : ℂ) * X + C c) ≠ 0 := by
    intro hzero
    have hdeg := congrArg Polynomial.natDegree hzero
    rw [natDegree_comp, hlinear] at hdeg
    simp at hdeg
    omega
  unfold polynomialAffineMonic
  exact monic_mul_leadingCoeff_inv hU

theorem polynomialAffineMonic_eval
    (P : ℂ[X]) (c : ℂ) (r : ℝ) (hr : r ≠ 0)
    (z : ℂ) :
    (polynomialAffineMonic P c r).eval z =
      P.eval (c + (r : ℂ) * z) /
        (P.leadingCoeff * (r : ℂ) ^ P.natDegree) := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hlinear : (C (r : ℂ) * X + C c : ℂ[X]).natDegree = 1 :=
    natDegree_linear hrc
  have hlead : (C (r : ℂ) * X + C c : ℂ[X]).leadingCoeff = r :=
    leadingCoeff_linear hrc
  unfold polynomialAffineMonic
  rw [eval_mul, eval_C, eval_comp,
    leadingCoeff_comp (by rw [hlinear]; decide), hlead]
  simp only [eval_add, eval_mul, eval_C, eval_X]
  ring

end SpringerLean

#print axioms SpringerLean.polynomialAffineMonic_natDegree
#print axioms SpringerLean.polynomialAffineMonic_monic
#print axioms SpringerLean.polynomialAffineMonic_eval
