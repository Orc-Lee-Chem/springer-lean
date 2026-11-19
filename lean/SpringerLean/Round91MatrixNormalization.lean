import SpringerLean.Round90FaberCombination

set_option maxHeartbeats 1000000

namespace SpringerLean

private theorem schober_sqrt_two_sq :
    ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))

private theorem schober_sqrt_three_sq :
    ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3))

private theorem schober_sqrt_six_eq :
    ((Real.sqrt 6 : ℝ) : ℂ) =
      (Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ) := by
  have h : (Real.sqrt 6 : ℝ) = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  exact_mod_cast h

private theorem schober_normalized_test_energy
    (v : Fin 3 → ℂ) :
    ‖v 0‖ ^ 2 +
      2 * ‖(Real.sqrt 2 : ℂ) / 2 * v 1‖ ^ 2 +
      3 * ‖(Real.sqrt 3 : ℂ) / 3 * v 2‖ ^ 2 =
      ∑ i : Fin 3, ‖v i‖ ^ 2 := by
  rw [Fin.sum_univ_three]
  have h2 : ‖(Real.sqrt 2 : ℂ) / 2‖ ^ 2 = 1 / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2)]
    have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hden : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    rw [hden]
    calc
      (Real.sqrt 2 / (2 : ℝ)) ^ 2 = (Real.sqrt 2) ^ 2 / 4 := by ring
      _ = 1 / 2 := by rw [hs]; norm_num
  have h3 : ‖(Real.sqrt 3 : ℂ) / 3‖ ^ 2 = 1 / 3 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 3)]
    have hs : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    have hden : ‖(3 : ℂ)‖ = (3 : ℝ) := by norm_num
    rw [hden]
    calc
      (Real.sqrt 3 / (3 : ℝ)) ^ 2 = (Real.sqrt 3) ^ 2 / 9 := by ring
      _ = 1 / 3 := by rw [hs]; norm_num
  rw [norm_mul, norm_mul, mul_pow, mul_pow, h2, h3]
  ring

private theorem schober_normalized_row_zero
    (b₁ b₂ b₃ b₄ b₅ : ℂ) (v : Fin 3 → ℂ) :
    (∑ j : Fin 3,
      schoberFiniteC b₁ b₂ b₃ b₄ b₅ 0 j * v j) =
      v 0 * b₁ +
        ((Real.sqrt 2 : ℂ) / 2 * v 1) * (2 * b₂) +
        ((Real.sqrt 3 : ℂ) / 3 * v 2) * (3 * b₃) := by
  rw [Fin.sum_univ_three]
  simp only [schoberFiniteC]
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two,
    Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceMul,
    Real.sqrt_one, mul_one, one_mul]
  rw [schoberKernelQ3_coeff_one_one,
    schoberKernelQ3_coeff_one_two,
    schoberKernelQ3_coeff_one_three]
  simp only [Complex.ofReal_one, one_mul]
  ring

private theorem schober_normalized_row_one
    (b₁ b₂ b₃ b₄ b₅ : ℂ) (v : Fin 3 → ℂ) :
    (∑ j : Fin 3,
      schoberFiniteC b₁ b₂ b₃ b₄ b₅ 1 j * v j) =
      (Real.sqrt 2 : ℂ) *
        (v 0 * b₂ +
          ((Real.sqrt 2 : ℂ) / 2 * v 1) * (2 * b₃ + b₁ ^ 2) +
          ((Real.sqrt 3 : ℂ) / 3 * v 2) *
            (3 * (b₄ + b₁ * b₂))) := by
  rw [Fin.sum_univ_three]
  simp only [schoberFiniteC]
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two,
    Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceMul,
    Real.sqrt_one, mul_one, one_mul]
  rw [schoberKernelQ3_coeff_two_one,
    schoberKernelQ3_coeff_two_two,
    schoberKernelQ3_coeff_two_three,
    schober_sqrt_six_eq]
  simp only [schoberQ22]
  have h4 : ((Real.sqrt 4 : ℝ) : ℂ) = 2 := by
    have hr : (Real.sqrt 4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    exact_mod_cast hr
  rw [h4]
  ring_nf
  simp only [schober_sqrt_two_sq]
  ring

private theorem schober_normalized_row_two
    (b₁ b₂ b₃ b₄ b₅ : ℂ) (v : Fin 3 → ℂ) :
    (∑ j : Fin 3,
      schoberFiniteC b₁ b₂ b₃ b₄ b₅ 2 j * v j) =
      (Real.sqrt 3 : ℂ) *
        (v 0 * b₃ +
          ((Real.sqrt 2 : ℂ) / 2 * v 1) *
            (2 * (b₄ + b₁ * b₂)) +
          ((Real.sqrt 3 : ℂ) / 3 * v 2) *
            (3 * b₅ + 3 * b₁ * b₃ + 3 * b₂ ^ 2 + b₁ ^ 3)) := by
  rw [Fin.sum_univ_three]
  simp only [schoberFiniteC]
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two,
    Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceMul,
    Real.sqrt_one, mul_one, one_mul]
  rw [schoberKernelQ3_coeff_three_one,
    schoberKernelQ3_coeff_three_two,
    schoberKernelQ3_coeff_three_three,
    schober_sqrt_six_eq]
  simp only [schoberQ33]
  have h9 : ((Real.sqrt 9 : ℝ) : ℂ) = 3 := by
    have hr : (Real.sqrt 9 : ℝ) = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    exact_mod_cast hr
  rw [h9]
  ring_nf
  simp only [schober_sqrt_three_sq]
  ring

private theorem schober_sqrt_two_norm_mul_sq (z : ℂ) :
    ‖(Real.sqrt 2 : ℂ) * z‖ ^ 2 = 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), Real.sq_sqrt (by norm_num)]

private theorem schober_sqrt_three_norm_mul_sq (z : ℂ) :
    ‖(Real.sqrt 3 : ℂ) * z‖ ^ 2 = 3 * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 3), Real.sq_sqrt (by norm_num)]

/-- Pure finite-dimensional normalization: the actual weighted Faber
inequality implies contraction of the symmetric square-root-weighted
three-by-three logarithmic-kernel matrix. -/
theorem schoberFiniteC_contraction_of_faber_quadratic
    (b₁ b₂ b₃ b₄ b₅ : ℂ)
    (hE : ∀ α₁ α₂ α₃ : ℂ,
      thirdFaberQuadraticEnergy b₁ b₂ b₃ b₄ b₅ α₁ α₂ α₃ ≤
        ‖α₁‖ ^ 2 + 2 * ‖α₂‖ ^ 2 + 3 * ‖α₃‖ ^ 2)
    (v : Fin 3 → ℂ) :
    (∑ i : Fin 3,
      ‖∑ j : Fin 3,
        schoberFiniteC b₁ b₂ b₃ b₄ b₅ i j * v j‖ ^ 2) ≤
      ∑ j : Fin 3, ‖v j‖ ^ 2 := by
  let α₁ : ℂ := v 0
  let α₂ : ℂ := (Real.sqrt 2 : ℂ) / 2 * v 1
  let α₃ : ℂ := (Real.sqrt 3 : ℂ) / 3 * v 2
  have h := hE α₁ α₂ α₃
  have hleft :
      (∑ i : Fin 3,
        ‖∑ j : Fin 3,
          schoberFiniteC b₁ b₂ b₃ b₄ b₅ i j * v j‖ ^ 2) =
      thirdFaberQuadraticEnergy b₁ b₂ b₃ b₄ b₅ α₁ α₂ α₃ := by
    rw [Fin.sum_univ_three,
      schober_normalized_row_zero,
      schober_normalized_row_one,
      schober_normalized_row_two]
    rw [schober_sqrt_two_norm_mul_sq,
      schober_sqrt_three_norm_mul_sq]
    rfl
  have hright :
      ‖α₁‖ ^ 2 + 2 * ‖α₂‖ ^ 2 + 3 * ‖α₃‖ ^ 2 =
        ∑ j : Fin 3, ‖v j‖ ^ 2 := by
    exact schober_normalized_test_energy v
  calc
    _ = thirdFaberQuadraticEnergy b₁ b₂ b₃ b₄ b₅ α₁ α₂ α₃ := hleft
    _ ≤ ‖α₁‖ ^ 2 + 2 * ‖α₂‖ ^ 2 + 3 * ‖α₃‖ ^ 2 := h
    _ = _ := hright

/-- Full three-by-three Grunsky contraction for the finite logarithmic
kernel of every actual centered exterior-univalent map. -/
theorem exterior_schoberFiniteC_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : Fin 3 → ℂ) :
    (∑ i : Fin 3,
      ‖∑ j : Fin 3,
        schoberFiniteC
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) i j * v j‖ ^ 2) ≤
      ∑ j : Fin 3, ‖v j‖ ^ 2 :=
  schoberFiniteC_contraction_of_faber_quadratic
    (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
    (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
    (exteriorForwardCoeff F 5)
    (exterior_faber_quadratic_energy_le F hc) v

/-- The sharp parameter bound for the actual fifth inverse coefficient. -/
theorem exteriorInverseCoeff_five_norm_le_one_add_firstCoeff_sq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorInverseCoeff F 5‖ ≤
      1 + ‖exteriorForwardCoeff F 1‖ ^ 2 :=
  exteriorInverseCoeff_five_norm_le_one_add_firstCoeff_sq_of_matrix_contraction
    F hc (exterior_schoberFiniteC_contraction F hc)

theorem exteriorInverseCoeff_five_norm_le_two
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorInverseCoeff F 5‖ ≤ 2 := by
  have hB := exteriorInverseCoeff_five_norm_le_one_add_firstCoeff_sq F hc
  have hb : ‖exteriorForwardCoeff F 1‖ ≤ 1 :=
    exteriorForwardCoeff_one_norm_le_of_finite_area F
      (fun N => exteriorForwardCoeff_finite_area F hc N)
  nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]

theorem exteriorInverseCoeff_five_norm_lt_two_of_firstCoeff_lt_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hb : ‖exteriorForwardCoeff F 1‖ < 1) :
    ‖exteriorInverseCoeff F 5‖ < 2 := by
  have hB := exteriorInverseCoeff_five_norm_le_one_add_firstCoeff_sq F hc
  nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]

/-- Full fifth-order equality classification on the original exterior
disk. The converse uses the already verified actual slit inverse series. -/
theorem exteriorInverseCoeff_five_norm_eq_two_iff_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorInverseCoeff F 5‖ = 2 ↔
      ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk := by
  constructor
  · intro hB
    have hb : ‖exteriorForwardCoeff F 1‖ ≤ 1 :=
      exteriorForwardCoeff_one_norm_le_of_finite_area F
        (fun N => exteriorForwardCoeff_finite_area F hc N)
    have hparam := exteriorInverseCoeff_five_norm_le_one_add_firstCoeff_sq F hc
    have hbeq : ‖exteriorForwardCoeff F 1‖ = 1 := by
      nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]
    obtain ⟨a, ha, hFG, _⟩ := exteriorInverseCoeff_five_endpoint F hc hbeq
    exact ⟨a, ha, hFG⟩
  · rintro ⟨a, ha, hFG⟩
    exact exteriorInverseCoeff_five_norm_eq_two_of_slit F hc a ha hFG

end SpringerLean
