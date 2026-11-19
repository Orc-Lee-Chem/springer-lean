import SpringerLean.Round2053UnitaryFirstColumn
import Mathlib.Analysis.MeanInequalitiesPow

open Matrix
open scoped ComplexConjugate

namespace SpringerLean

theorem unitary_column_norm_square_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (j : ι) :
    ∑ i, ‖U i j‖ ^ 2 = 1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ => A j j) hU
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.conj_mul', Matrix.one_apply_eq] at h
  exact_mod_cast h

theorem unitary_row_norm_square_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) (i : ι) :
    ∑ j, ‖U i j‖ ^ 2 = 1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ => A i i) hU
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.mul_conj', Matrix.one_apply_eq] at h
  exact_mod_cast h

theorem unitary_conjugate_diagonal_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (d : ι → ℂ) (j : ι) :
    (Uᴴ * diagonal d * U) j j = ∑ i, ((‖U i j‖ ^ 2 : ℝ) : ℂ) * d i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.star_def,
    mul_right_comm, Complex.conj_mul']
  push_cast
  rfl

theorem unitary_diagonal_entry_norm_power_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (d : ι → ℂ)
    (j : ι) (p : ℝ) (hp : 1 ≤ p) :
    ‖(Uᴴ * diagonal d * U) j j‖ ^ p ≤ ∑ i, ‖U i j‖ ^ 2 * ‖d i‖ ^ p := by
  let w (i : ι) := ‖U i j‖ ^ 2
  have hws : ∑ i, w i = 1 := unitary_column_norm_square_sum U hU j
  have hw (i : ι) : 0 ≤ w i := sq_nonneg _
  have hnorm : ‖(Uᴴ * diagonal d * U) j j‖ ≤ ∑ i, w i * ‖d i‖ := by
    rw [unitary_conjugate_diagonal_entry]
    calc
      _ ≤ ∑ i, ‖(w i : ℂ) * d i‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
  refine (Real.rpow_le_rpow (norm_nonneg _) hnorm (by linarith)).trans ?_
  exact (convexOn_rpow hp).map_sum_le (fun i _ => hw i) hws
    (fun i _ => norm_nonneg (d i))

/-- Summing the diagonal Jensen inequalities on the compressed block
uses the constant deleted column to yield the exact normalized mean. -/
theorem unitary_uniform_compression_diagonal_power_sum
    (n : ℕ) (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hU₁ : Uᴴ * U = 1) (hU₂ : U * Uᴴ = 1)
    (hU₀ : ∀ i, ‖U i 0‖ ^ 2 = ((n+1 : ℕ) : ℝ)⁻¹)
    (d : Fin (n+1) → ℂ) (p : ℝ) (hp : 1 ≤ p) :
    (∑ j : Fin n, ‖(Uᴴ * diagonal d * U) j.succ j.succ‖ ^ p) ≤
      (n : ℝ) / ((n+1 : ℕ) : ℝ) * (∑ i : Fin (n+1), ‖d i‖ ^ p) := by
  calc
    _ ≤ ∑ j : Fin n, ∑ i : Fin (n+1), ‖U i j.succ‖ ^ 2 * ‖d i‖ ^ p :=
      Finset.sum_le_sum (fun j _ => unitary_diagonal_entry_norm_power_le U hU₁ d j.succ p hp)
    _ = ∑ i : Fin (n+1), (∑ j : Fin n, ‖U i j.succ‖ ^ 2) * ‖d i‖ ^ p := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hrow := unitary_row_norm_square_sum U hU₂ i
      rw [Fin.sum_univ_succ, hU₀] at hrow
      congr 1
      have hpos : 0 < ((n+1 : ℕ) : ℝ) := by positivity
      apply (eq_div_iff hpos.ne').mpr
      have hsum : (∑ j : Fin n, ‖U i j.succ‖ ^ 2) =
          1 - ((n+1 : ℕ) : ℝ)⁻¹ := by linarith
      rw [hsum]
      push_cast
      field_simp [show (n : ℝ) + 1 ≠ 0 by positivity]
      ring

end SpringerLean
