import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots

open Matrix Polynomial

namespace SpringerLean

/-- Adjugation commutes with a change of basis. The proof uses only
adjugate multiplication and therefore also applies at singular matrices. -/
theorem adjugate_matrix_similarity {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (A S T : Matrix ι ι R)
    (hST : S * T = 1) (hTS : T * S = 1) :
    (T * A * S).adjugate = T * A.adjugate * S := by
  have hS : S.adjugate = S.det • T := by
    calc
      _ = S.adjugate * (S * T) := by rw [hST, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hT : T.adjugate = T.det • S := by
    calc
      _ = T.adjugate * (T * S) := by rw [hTS, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hdet : S.det * T.det = 1 := by
    simpa [det_mul] using congrArg Matrix.det hST
  rw [adjugate_mul_distrib, adjugate_mul_distrib, hS, hT,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hdet, one_smul,
    Matrix.mul_assoc]

/-- Removing the first row and column after changing basis gives a
weighted sum of the diagonal cofactors. -/
theorem det_diagonal_compression
    {R : Type*} [CommRing R] {n : ℕ}
    (d : Fin (n+1) → R) (S T : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (hST : S * T = 1) (hTS : T * S = 1) :
    (((T * diagonal d * S).submatrix (0 : Fin (n+1)).succAbove
      (0 : Fin (n+1)).succAbove)).det =
      ∑ i : Fin (n+1), T 0 i * S i 0 * (∏ j ∈ Finset.univ.erase i, d j) := by
  have hco := adjugate_fin_succ_eq_det_submatrix (T * diagonal d * S)
    (0 : Fin (n+1)) (0 : Fin (n+1))
  simp only [Fin.val_zero, add_zero, pow_zero, one_mul] at hco
  rw [← hco, adjugate_matrix_similarity _ S T hST hTS, adjugate_diagonal,
    Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_diagonal]
  ring

/-- The characteristic polynomial of the compression is the divided
derivative when the deleted basis vector gives uniform weights. -/
theorem charpoly_uniform_diagonal_compression
    {R : Type*} [CommRing R] [IsDomain R] [Infinite R] {n : ℕ}
    (d : Fin (n+1) → R) (S T : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (hST : S * T = 1) (hTS : T * S = 1)
    (c : R) (hweight : ∀ i, T 0 i * S i 0 = c) :
    ((T * diagonal d * S).submatrix (0 : Fin (n+1)).succAbove
      (0 : Fin (n+1)).succAbove).charpoly =
      C c * (∏ i : Fin (n+1), (X - C (d i))).derivative := by
  classical
  let e := (0 : Fin (n+1)).succAbove
  let A := T * diagonal d * S
  apply Polynomial.funext
  intro x
  rw [eval_charpoly, eval_mul, eval_C, derivative_prod_finset, eval_finsetSum]
  simp only [derivative_sub, derivative_X, derivative_C, sub_zero, mul_one,
    eval_prod, eval_sub, eval_X, eval_C]
  have heq : Matrix.scalar (Fin n) x - A.submatrix e e =
      ((T * diagonal (fun i => x - d i) * S).submatrix e e) := by
    have hd : diagonal (fun i => x - d i) =
        Matrix.scalar (Fin (n+1)) x - diagonal d := by
      rw [Matrix.scalar_apply, diagonal_sub]
    rw [hd, Matrix.mul_sub, Matrix.sub_mul]
    have hcentral : T * Matrix.scalar (Fin (n+1)) x * S = Matrix.scalar (Fin (n+1)) x := by
      rw [show T * Matrix.scalar (Fin (n+1)) x = Matrix.scalar (Fin (n+1)) x * T by
        ext i j
        simp [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm],
        Matrix.mul_assoc, hTS, Matrix.mul_one]
    rw [hcentral]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [A, Matrix.scalar_apply]
    · have heij : e i ≠ e j := fun h => hij (Fin.succAbove_right_injective h)
      simp [A, Matrix.scalar_apply, Matrix.diagonal_apply_ne, hij, heij]
  change (Matrix.scalar (Fin n) x - A.submatrix e e).det = _
  rw [heq]
  change ((T * diagonal (fun i => x - d i) * S).submatrix
    (0 : Fin (n+1)).succAbove (0 : Fin (n+1)).succAbove).det = _
  rw [det_diagonal_compression _ S T hST hTS, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [hweight])

end SpringerLean
