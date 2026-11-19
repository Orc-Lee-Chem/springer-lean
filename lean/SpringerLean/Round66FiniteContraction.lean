import SpringerLean.Round65BivariateKernel

set_option maxHeartbeats 100000

namespace SpringerLean

/-- A complex bilinear form is bounded by the squared ℓ² norm when its
associated finite matrix is a contraction. No conjugation is assumed in the
bilinear form; absolute values make the usual Cauchy–Schwarz proof valid. -/
theorem finiteComplexBilinear_norm_le_of_l2_contraction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → ι → ℂ)
    (hC : ∀ v : ι → ℂ,
      (∑ i : ι, ‖∑ j : ι, C i j * v j‖ ^ 2) ≤
        ∑ j : ι, ‖v j‖ ^ 2)
    (v : ι → ℂ) :
    ‖∑ i : ι, v i * (∑ j : ι, C i j * v j)‖ ≤
      ∑ i : ι, ‖v i‖ ^ 2 := by
  let y : ι → ℂ := fun i => ∑ j : ι, C i j * v j
  let S : ℝ := ∑ i : ι, ‖v i‖ ^ 2
  let P : ℝ := ∑ i : ι, ‖v i‖ * ‖y i‖
  have hS : 0 ≤ S := Finset.sum_nonneg (by intro i hi; positivity)
  have hP : 0 ≤ P := Finset.sum_nonneg (by intro i hi; positivity)
  have hnorm : ‖∑ i : ι, v i * y i‖ ≤ P := by
    calc
      ‖∑ i : ι, v i * y i‖ ≤ ∑ i : ι, ‖v i * y i‖ := norm_sum_le _ _
      _ = P := by simp [P, norm_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : ι => ‖v i‖) (fun i : ι => ‖y i‖)
  have hcontract : (∑ i : ι, ‖y i‖ ^ 2) ≤ S := hC v
  have hP2 : P ^ 2 ≤ S ^ 2 := by
    calc
      P ^ 2 ≤ S * (∑ i : ι, ‖y i‖ ^ 2) := by simpa [P, S] using hcs
      _ ≤ S * S := mul_le_mul_of_nonneg_left hcontract hS
      _ = S ^ 2 := by ring
  have hnorm2 : ‖∑ i : ι, v i * y i‖ ^ 2 ≤ P ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hP).2 hnorm
  exact (sq_le_sq₀ (norm_nonneg _) hS).1 (hnorm2.trans hP2)


/-- The weighted 3×3 coefficient matrix of the finite logarithmic kernel. -/
noncomputable def schoberFiniteC (b1 b2 b3 b4 b5 : ℂ)
    (i j : Fin 3) : ℂ :=
  (Real.sqrt (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ)) : ℂ) *
    schoberBiCoeff (i.val + 1) (j.val + 1)
      (schoberKernelQ3 b1 b2 b3 b4 b5)

noncomputable def schoberTestVectorOne (b1 : ℂ) : Fin 3 → ℂ :=
  fun i => if i = 0 then b1 else if i = 1 then 0 else
    (Real.sqrt 3 : ℂ)⁻¹

theorem schoberTestVectorOne_energy (b1 : ℂ) :
    (∑ i : Fin 3, ‖schoberTestVectorOne b1 i‖ ^ 2) =
      ‖b1‖ ^ 2 + 1 / 3 := by
  rw [Fin.sum_univ_three]
  simp [schoberTestVectorOne, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 3)]


/-- The d=1 Schober contribution is the bilinear form of the weighted kernel matrix. -/
theorem schoberFiniteLinear_eq_matrix_bilinear
    (b1 b2 b3 b4 b5 : ℂ) :
    schoberFiniteLinear b1 b2 b3 b5 =
      ∑ i : Fin 3,
        schoberTestVectorOne b1 i *
          (∑ j : Fin 3,
            schoberFiniteC b1 b2 b3 b4 b5 i j *
              schoberTestVectorOne b1 j) := by
  simp [Fin.sum_univ_three, schoberTestVectorOne, schoberFiniteC,
    schoberFiniteLinear, schoberQ11, schoberQ13, schoberQ33,
    schoberKernelQ3_coeff_one_one, schoberKernelQ3_coeff_one_three,
    schoberKernelQ3_coeff_three_one, schoberKernelQ3_coeff_three_three]
  have h9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 3))
  have hsq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3))
  have hr : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ = 1 := by
    exact mul_inv_cancel₀ h3
  have hr2 : (3 : ℂ) * ((Real.sqrt 3 : ℂ)⁻¹) ^ 2 = 1 := by
    rw [← hsq, ← mul_pow, hr]
    norm_num
  norm_num only [Nat.reduceAdd, Nat.reduceMul] at *
  rw [h9]
  let q : ℂ := b5 + b1 * b3 + b2 ^ 2 + b1 ^ 3 / 3
  calc
    _ = b1 ^ 3 + 2 * b1 * b3 + q := by dsimp [q]; ring
    _ = b1 ^ 3 + 2 * b1 * b3 *
          ((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹) +
          ((3 : ℂ) * ((Real.sqrt 3 : ℂ)⁻¹) ^ 2) * q := by
            rw [hr, hr2]
            ring
    _ = _ := by dsimp [q]; ring

/-- The first of the three finite Schober norm estimates follows from the
weighted 3×3 matrix contraction. The contraction still requires proof from
univalence before this can enter a paper-level result. -/
theorem schoberFiniteLinear_norm_le_of_matrix_contraction
    (b1 b2 b3 b4 b5 : ℂ)
    (hC : ∀ v : Fin 3 → ℂ,
      (∑ i : Fin 3,
        ‖∑ j : Fin 3, schoberFiniteC b1 b2 b3 b4 b5 i j * v j‖ ^ 2) ≤
        ∑ j : Fin 3, ‖v j‖ ^ 2) :
    ‖schoberFiniteLinear b1 b2 b3 b5‖ ≤ ‖b1‖ ^ 2 + 1 / 3 := by
  rw [schoberFiniteLinear_eq_matrix_bilinear]
  exact (finiteComplexBilinear_norm_le_of_l2_contraction
    (schoberFiniteC b1 b2 b3 b4 b5) hC (schoberTestVectorOne b1)).trans_eq
      (schoberTestVectorOne_energy b1)
end SpringerLean