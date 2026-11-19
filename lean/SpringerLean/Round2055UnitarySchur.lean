import SpringerLean.Round2054SchurEigenvector
import Mathlib.Data.Matrix.Block

open Matrix

namespace SpringerLean

def unitarySchurExtend {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
    (fun i' => Fin.cases 0 (fun j' => V i' j') j) i

@[simp] theorem unitarySchurExtend_zero_zero {n : ℕ}
    (V : Matrix (Fin n) (Fin n) ℂ) : unitarySchurExtend V 0 0 = 1 := rfl

@[simp] theorem unitarySchurExtend_zero_succ {n : ℕ}
    (V : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : unitarySchurExtend V 0 j.succ = 0 := rfl

@[simp] theorem unitarySchurExtend_succ_zero {n : ℕ}
    (V : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : unitarySchurExtend V i.succ 0 = 0 := rfl

@[simp] theorem unitarySchurExtend_succ_succ {n : ℕ}
    (V : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    unitarySchurExtend V i.succ j.succ = V i j := rfl

theorem unitarySchurExtend_conjTranspose {n : ℕ}
    (V : Matrix (Fin n) (Fin n) ℂ) :
    (unitarySchurExtend V)ᴴ = unitarySchurExtend Vᴴ := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · exact Fin.cases (by simp) (fun j => by simp) j
  · exact Fin.cases (by simp) (fun j => by simp) j

theorem unitarySchurExtend_mul {n : ℕ}
    (V W : Matrix (Fin n) (Fin n) ℂ) :
    unitarySchurExtend V * unitarySchurExtend W = unitarySchurExtend (V * W) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · exact Fin.cases (by simp [Matrix.mul_apply, Fin.sum_univ_succ])
      (fun j => by simp [Matrix.mul_apply, Fin.sum_univ_succ]) j
  · exact Fin.cases (by simp [Matrix.mul_apply, Fin.sum_univ_succ])
      (fun j => by simp [Matrix.mul_apply, Fin.sum_univ_succ]) j

@[simp] theorem unitarySchurExtend_one (n : ℕ) :
    unitarySchurExtend (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · exact Fin.cases (by simp) (fun j => by simp [Matrix.one_apply, (Fin.succ_ne_zero j).symm]) j
  · exact Fin.cases (by simp)
      (fun j => by simp [Matrix.one_apply]) j

theorem unitarySchurExtend_conjugate_succ_succ {n : ℕ}
    (D : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    ((unitarySchurExtend V)ᴴ * D * unitarySchurExtend V) i.succ j.succ =
      (Vᴴ * D.submatrix Fin.succ Fin.succ * V) i j := by
  rw [unitarySchurExtend_conjTranspose]
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, unitarySchurExtend_succ_zero,
    unitarySchurExtend_zero_succ, unitarySchurExtend_succ_succ, Matrix.submatrix_apply,
    zero_mul, mul_zero, zero_add]

private theorem unitarySchurExtend_conjugate_succ_zero {n : ℕ}
    (D : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (hcol : ∀ i : Fin n, D i.succ 0 = 0) (i : Fin n) :
    ((unitarySchurExtend V)ᴴ * D * unitarySchurExtend V) i.succ 0 = 0 := by
  rw [unitarySchurExtend_conjTranspose]
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, unitarySchurExtend_succ_zero,
    unitarySchurExtend_zero_zero, unitarySchurExtend_succ_succ, hcol, zero_mul, mul_zero,
    zero_add, mul_one, Finset.sum_const_zero]

/-- Complex Schur triangularization in a unitary basis. No
normality or diagonalizability hypothesis is used. -/
theorem exists_unitary_schur_triangular (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      (Uᴴ * A * U).BlockTriangular id := by
  induction n with
  | zero =>
    exact ⟨1, by simp, by simp, fun {i} => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨U, hU₁, hU₂, hcol⟩ := exists_unitary_first_column_eigenvector n A
    let D := Uᴴ * A * U
    obtain ⟨V, hV₁, hV₂, hV⟩ := ih (D.submatrix Fin.succ Fin.succ)
    let E := unitarySchurExtend V
    have hE₁ : Eᴴ * E = 1 := by
      dsimp [E]
      rw [unitarySchurExtend_conjTranspose, unitarySchurExtend_mul, hV₁,
        unitarySchurExtend_one]
    have hE₂ : E * Eᴴ = 1 := by
      dsimp [E]
      rw [unitarySchurExtend_conjTranspose, unitarySchurExtend_mul, hV₂,
        unitarySchurExtend_one]
    refine ⟨U * E, ?_, ?_, ?_⟩
    · simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U E, hU₁, Matrix.one_mul, hE₁]
    · simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc E Eᴴ Uᴴ, hE₂, Matrix.one_mul, hU₂]
    · have hEq : (U * E)ᴴ * A * (U * E) = Eᴴ * D * E := by
        simp [D, Matrix.mul_assoc]
      rw [hEq]
      intro i j hij
      change j < i at hij
      revert hij
      refine Fin.cases ?_ (fun i => ?_) i
      · exact fun h => (not_lt_of_ge (Fin.zero_le j) h).elim
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          exact unitarySchurExtend_conjugate_succ_zero D V hcol i
        · intro hij
          rw [unitarySchurExtend_conjugate_succ_succ]
          exact hV (Fin.succ_lt_succ_iff.mp hij)

end SpringerLean
