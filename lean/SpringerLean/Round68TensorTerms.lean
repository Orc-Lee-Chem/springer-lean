import SpringerLean.Round67TensorContraction

namespace SpringerLean

noncomputable def schoberTestVectorTwo : Fin 3 × Fin 3 → ℂ :=
  fun p => if p = (0, 1) ∨ p = (1, 0) then
    (Real.sqrt 2 : ℂ)⁻¹ else 0

theorem schoberTestVectorTwo_energy :
    (∑ p : Fin 3 × Fin 3, ‖schoberTestVectorTwo p‖ ^ 2) = 1 := by
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_three, schoberTestVectorTwo, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
  norm_num


/-- The quadratic finite Schober contribution is half the bilinear tensor form. -/
theorem schoberFiniteQuadratic_eq_tensor_bilinear
    (b1 b2 b3 b4 b5 : ℂ) :
    2 * schoberFiniteQuadratic b1 b2 b3 =
      ∑ p : Fin 3 × Fin 3,
        schoberTestVectorTwo p *
          (∑ q : Fin 3 × Fin 3,
            (schoberFiniteC b1 b2 b3 b4 b5 p.1 q.1 *
              schoberFiniteC b1 b2 b3 b4 b5 p.2 q.2) *
              schoberTestVectorTwo q) := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_three,
    schoberTestVectorTwo, schoberFiniteC, schoberFiniteQuadratic,
    schoberQ11, schoberQ12, schoberQ22,
    schoberKernelQ3_coeff_one_one, schoberKernelQ3_coeff_one_two,
    schoberKernelQ3_coeff_two_one, schoberKernelQ3_coeff_two_two]
  have hroot : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 2))
  have hfactor : (Real.sqrt 2 : ℂ) ^ 2 * ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hroot]
    norm_num
  calc
    _ = (b1 * b3 * 2 + b1 ^ 3 + b2 ^ 2 * 2) *
        ((Real.sqrt 2 : ℂ) ^ 2 * ((Real.sqrt 2 : ℂ)⁻¹) ^ 2) := by
          rw [hfactor]
          ring
    _ = _ := by ring

/-- The d=2 contribution is at most 1/2 under the actual 3×3 matrix bound. -/
theorem schoberFiniteQuadratic_norm_le_of_matrix_contraction
    (b1 b2 b3 b4 b5 : ℂ)
    (hC : ∀ v : Fin 3 → ℂ,
      (∑ i : Fin 3,
        ‖∑ j : Fin 3, schoberFiniteC b1 b2 b3 b4 b5 i j * v j‖ ^ 2) ≤
        ∑ j : Fin 3, ‖v j‖ ^ 2) :
    ‖schoberFiniteQuadratic b1 b2 b3‖ ≤ 1 / 2 := by
  let C := schoberFiniteC b1 b2 b3 b4 b5
  have hTT := finiteComplexTensor_contraction C C hC hC
  have hbil := finiteComplexBilinear_norm_le_of_l2_contraction
    (fun p q : Fin 3 × Fin 3 => C p.1 q.1 * C p.2 q.2)
    hTT schoberTestVectorTwo
  rw [← schoberFiniteQuadratic_eq_tensor_bilinear,
    schoberTestVectorTwo_energy] at hbil
  norm_num [norm_mul] at hbil ⊢
  linarith

/-- For actual exterior maps the cubic term uses the already proved area bound
`‖b₁‖ ≤ 1`, so no additional tensor API is needed at degree three. -/
theorem schoberFiniteCubic_norm_le_of_first_norm_le
    (b1 : ℂ) (hb1 : ‖b1‖ ≤ 1) :
    ‖schoberFiniteCubic b1‖ ≤ 1 / 6 := by
  have h0 : 0 ≤ ‖b1‖ := norm_nonneg _
  have hpow : ‖b1‖ ^ 3 ≤ (1 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb1)
      (by positivity : 0 ≤ 1 + ‖b1‖ + ‖b1‖ ^ 2)]
  simpa [schoberFiniteCubic, schoberQ11, norm_div, norm_pow] using
    (div_le_div_of_nonneg_right hpow (by norm_num : (0 : ℝ) ≤ 6))

/-- Conditional paper-level reduction: the sole remaining analytic input is
that the concrete finite matrix of the actual map is an ℓ² contraction. -/
theorem exteriorInverseCoeff_five_norm_le_one_add_firstCoeff_sq_of_matrix_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hC : ∀ v : Fin 3 → ℂ,
      (∑ i : Fin 3,
        ‖∑ j : Fin 3,
          schoberFiniteC
            (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
            (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
            (exteriorForwardCoeff F 5) i j * v j‖ ^ 2) ≤
        ∑ j : Fin 3, ‖v j‖ ^ 2) :
    ‖exteriorInverseCoeff F 5‖ ≤ 1 + ‖exteriorForwardCoeff F 1‖ ^ 2 := by
  let b1 := exteriorForwardCoeff F 1
  let b2 := exteriorForwardCoeff F 2
  let b3 := exteriorForwardCoeff F 3
  let b4 := exteriorForwardCoeff F 4
  let b5 := exteriorForwardCoeff F 5
  have hlin := schoberFiniteLinear_norm_le_of_matrix_contraction
    b1 b2 b3 b4 b5 hC
  have hquad := schoberFiniteQuadratic_norm_le_of_matrix_contraction
    b1 b2 b3 b4 b5 hC
  have hfirst : ‖b1‖ ≤ 1 :=
    exteriorForwardCoeff_one_norm_le_of_finite_area F
      (fun N => exteriorForwardCoeff_finite_area F hc N)
  have hcub := schoberFiniteCubic_norm_le_of_first_norm_le b1 hfirst
  rw [exteriorInverseCoeff_five_eq_schoberFiniteContributions F hc]
  calc
    ‖schoberFiniteLinear b1 b2 b3 b5 +
        schoberFiniteQuadratic b1 b2 b3 + schoberFiniteCubic b1‖ ≤
      ‖schoberFiniteLinear b1 b2 b3 b5‖ +
        ‖schoberFiniteQuadratic b1 b2 b3‖ + ‖schoberFiniteCubic b1‖ := by
          calc
            _ ≤ ‖schoberFiniteLinear b1 b2 b3 b5 +
                schoberFiniteQuadratic b1 b2 b3‖ + ‖schoberFiniteCubic b1‖ :=
              norm_add_le _ _
            _ ≤ _ := by
              simpa [add_comm, add_left_comm, add_assoc] using
                (add_le_add_right (norm_add_le
                  (schoberFiniteLinear b1 b2 b3 b5)
                  (schoberFiniteQuadratic b1 b2 b3))
                  ‖schoberFiniteCubic b1‖)
    _ ≤ 1 + ‖b1‖ ^ 2 := by linarith
end SpringerLean