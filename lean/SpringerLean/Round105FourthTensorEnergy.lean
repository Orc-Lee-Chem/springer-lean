import SpringerLean.Round104SeventhCoeff
import SpringerLean.Round103NormalizeFour

set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

namespace SpringerLean

/-- The actual four-dimensional square-root-normalized Grunsky matrix,
with output index first and input index second. -/
noncomputable def schoberActualC4 (F : ℂ → ℂ)
    (j i : Fin 4) : ℂ :=
  ((Real.sqrt ((j.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
    ((Real.sqrt ((i.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
      schoberBiCoeff (j.val + 1) (i.val + 1)
        (schoberKernelQ4
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7))

theorem schoberActualC4_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : Fin 4 → ℂ) :
    (∑ j : Fin 4,
      ‖∑ i : Fin 4, schoberActualC4 F j i * v i‖ ^ 2) ≤
      ∑ i : Fin 4, ‖v i‖ ^ 2 := by
  simpa only [schoberActualC4] using
    exterior_schoberKernelQ4_normalized_contraction F hc v

theorem schoberActualC4_bilinear_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : Fin 4 → ℂ) :
    ‖∑ j : Fin 4,
      v j * (∑ i : Fin 4, schoberActualC4 F j i * v i)‖ ≤
      ∑ i : Fin 4, ‖v i‖ ^ 2 :=
  finiteComplexBilinear_norm_le_of_l2_contraction
    (schoberActualC4 F) (schoberActualC4_contraction F hc) v

noncomputable def schoberActualC4Tensor2 (F : ℂ → ℂ)
    (p q : Fin 4 × Fin 4) : ℂ :=
  schoberActualC4 F p.1 q.1 * schoberActualC4 F p.2 q.2

noncomputable def schoberActualC4Tensor3 (F : ℂ → ℂ)
    (p q : (Fin 4 × Fin 4) × Fin 4) : ℂ :=
  schoberActualC4Tensor2 F p.1 q.1 * schoberActualC4 F p.2 q.2

noncomputable def schoberActualC4Tensor4 (F : ℂ → ℂ)
    (p q : ((Fin 4 × Fin 4) × Fin 4) × Fin 4) : ℂ :=
  schoberActualC4Tensor3 F p.1 q.1 * schoberActualC4 F p.2 q.2

theorem schoberActualC4Tensor2_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : Fin 4 × Fin 4 → ℂ) :
    (∑ p : Fin 4 × Fin 4,
      ‖∑ q : Fin 4 × Fin 4,
        schoberActualC4Tensor2 F p q * v q‖ ^ 2) ≤
      ∑ q : Fin 4 × Fin 4, ‖v q‖ ^ 2 := by
  simpa only [schoberActualC4Tensor2] using
    finiteComplexTensor_contraction (schoberActualC4 F) (schoberActualC4 F)
      (schoberActualC4_contraction F hc)
      (schoberActualC4_contraction F hc) v

theorem schoberActualC4Tensor3_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : (Fin 4 × Fin 4) × Fin 4 → ℂ) :
    (∑ p : (Fin 4 × Fin 4) × Fin 4,
      ‖∑ q : (Fin 4 × Fin 4) × Fin 4,
        schoberActualC4Tensor3 F p q * v q‖ ^ 2) ≤
      ∑ q : (Fin 4 × Fin 4) × Fin 4, ‖v q‖ ^ 2 := by
  simpa only [schoberActualC4Tensor3] using
    finiteComplexTensor_contraction
      (schoberActualC4Tensor2 F) (schoberActualC4 F)
      (schoberActualC4Tensor2_contraction F hc)
      (schoberActualC4_contraction F hc) v

theorem schoberActualC4Tensor4_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : ((Fin 4 × Fin 4) × Fin 4) × Fin 4 → ℂ) :
    (∑ p : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
      ‖∑ q : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
        schoberActualC4Tensor4 F p q * v q‖ ^ 2) ≤
      ∑ q : ((Fin 4 × Fin 4) × Fin 4) × Fin 4, ‖v q‖ ^ 2 := by
  simpa only [schoberActualC4Tensor4] using
    finiteComplexTensor_contraction
      (schoberActualC4Tensor3 F) (schoberActualC4 F)
      (schoberActualC4Tensor3_contraction F hc)
      (schoberActualC4_contraction F hc) v

theorem schoberActualC4Tensor2_bilinear_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : Fin 4 × Fin 4 → ℂ) :
    ‖∑ p : Fin 4 × Fin 4,
      v p * (∑ q : Fin 4 × Fin 4,
        schoberActualC4Tensor2 F p q * v q)‖ ≤
      ∑ p : Fin 4 × Fin 4, ‖v p‖ ^ 2 :=
  finiteComplexBilinear_norm_le_of_l2_contraction
    (schoberActualC4Tensor2 F) (schoberActualC4Tensor2_contraction F hc) v

theorem schoberActualC4Tensor3_bilinear_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : (Fin 4 × Fin 4) × Fin 4 → ℂ) :
    ‖∑ p : (Fin 4 × Fin 4) × Fin 4,
      v p * (∑ q : (Fin 4 × Fin 4) × Fin 4,
        schoberActualC4Tensor3 F p q * v q)‖ ≤
      ∑ p : (Fin 4 × Fin 4) × Fin 4, ‖v p‖ ^ 2 :=
  finiteComplexBilinear_norm_le_of_l2_contraction
    (schoberActualC4Tensor3 F) (schoberActualC4Tensor3_contraction F hc) v

theorem schoberActualC4Tensor4_bilinear_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : ((Fin 4 × Fin 4) × Fin 4) × Fin 4 → ℂ) :
    ‖∑ p : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
      v p * (∑ q : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
        schoberActualC4Tensor4 F p q * v q)‖ ≤
      ∑ p : ((Fin 4 × Fin 4) × Fin 4) × Fin 4, ‖v p‖ ^ 2 :=
  finiteComplexBilinear_norm_le_of_l2_contraction
    (schoberActualC4Tensor4 F) (schoberActualC4Tensor4_contraction F hc) v

/-- The order-four inverse coefficient functional, expressed on individual
negative monomials under the project's actual inverse sign convention. -/
noncomputable def schoberFourthL (B₁ B₂ : ℂ) (j : ℕ) : ℂ :=
  if j = 1 then B₂ else if j = 2 then 2 * B₁ else if j = 4 then 1 else 0

private theorem schober_norm_div_sqrt_sq (z : ℂ) (m : ℕ) (hm : 0 < m) :
    ‖z / (Real.sqrt (m : ℝ) : ℂ)‖ ^ 2 = ‖z‖ ^ 2 / (m : ℝ) := by
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]

noncomputable def schoberFourthV1 (B₁ B₂ : ℂ) (i : Fin 4) : ℂ :=
  schoberFourthL B₁ B₂ (i.val + 1) /
    (Real.sqrt ((i.val + 1 : ℕ) : ℝ) : ℂ)

theorem schoberActualA_row_four_eq_L
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (j : Fin 4) :
    schoberActualA F 4 (j.val + 1) =
      schoberFourthL (exteriorInverseCoeff F 1) (exteriorInverseCoeff F 2)
        (j.val + 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := schoberActualA_row_four F hc
  fin_cases j <;>
    simp [schoberFourthL, h1, h2, h3, h4]

/-- The d=1 comparison-kernel energy at inverse order four. -/
theorem schoberFourthL_linear_energy (B₁ B₂ : ℂ) :
    (∑ i : Fin 4,
      ‖schoberFourthL B₁ B₂ (i.val + 1)‖ ^ 2 /
        ((i.val + 1 : ℕ) : ℝ)) =
      ‖B₂‖ ^ 2 + 2 * ‖B₁‖ ^ 2 + 1 / 4 := by
  simp [Fin.sum_univ_four, schoberFourthL, norm_mul]
  ring

theorem schoberFourthV1_energy (B₁ B₂ : ℂ) :
    (∑ i : Fin 4, ‖schoberFourthV1 B₁ B₂ i‖ ^ 2) =
      ‖B₂‖ ^ 2 + 2 * ‖B₁‖ ^ 2 + 1 / 4 := by
  calc
    _ = ∑ i : Fin 4,
        ‖schoberFourthL B₁ B₂ (i.val + 1)‖ ^ 2 /
          ((i.val + 1 : ℕ) : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            exact schober_norm_div_sqrt_sq _ _ (by omega)
    _ = _ := schoberFourthL_linear_energy B₁ B₂

/-- The d=2 comparison-kernel energy, before division by 2!. -/
theorem schoberFourthL_quadratic_energy (B₁ B₂ : ℂ) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      ‖schoberFourthL B₁ B₂ (i.val + j.val + 2)‖ ^ 2 /
        (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ))) =
      4 * ‖B₁‖ ^ 2 + 11 / 12 := by
  simp [Fin.sum_univ_four, schoberFourthL, norm_mul]
  ring

noncomputable def schoberFourthV2 (B₁ B₂ : ℂ)
    (p : Fin 4 × Fin 4) : ℂ :=
  schoberFourthL B₁ B₂ (p.1.val + p.2.val + 2) /
    (Real.sqrt ((((p.1.val + 1) * (p.2.val + 1) : ℕ) : ℝ)) : ℂ)

theorem schoberFourthV2_energy (B₁ B₂ : ℂ) :
    (∑ p : Fin 4 × Fin 4, ‖schoberFourthV2 B₁ B₂ p‖ ^ 2) =
      4 * ‖B₁‖ ^ 2 + 11 / 12 := by
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4,
        ‖schoberFourthL B₁ B₂ (i.val + j.val + 2)‖ ^ 2 /
          (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ)) := by
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            simpa only [schoberFourthV2, Nat.cast_mul] using
              (schober_norm_div_sqrt_sq
                (schoberFourthL B₁ B₂ (i.val + j.val + 2))
                ((i.val + 1) * (j.val + 1)) (by positivity))
    _ = _ := schoberFourthL_quadratic_energy B₁ B₂

/-- The d=3 comparison-kernel energy, before division by 3!. -/
theorem schoberFourthL_cubic_energy (B₁ B₂ : ℂ) :
    (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4,
      ‖schoberFourthL B₁ B₂ (i.val + j.val + k.val + 3)‖ ^ 2 /
        (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) *
          ((k.val + 1 : ℕ) : ℝ))) =
      3 / 2 := by
  simp [Fin.sum_univ_four, schoberFourthL, norm_mul]
  ring

noncomputable def schoberFourthV3 (B₁ B₂ : ℂ)
    (p : (Fin 4 × Fin 4) × Fin 4) : ℂ :=
  schoberFourthL B₁ B₂ (p.1.1.val + p.1.2.val + p.2.val + 3) /
    (Real.sqrt (((((p.1.1.val + 1) * (p.1.2.val + 1) *
      (p.2.val + 1) : ℕ) : ℝ))) : ℂ)

theorem schoberFourthV3_energy (B₁ B₂ : ℂ) :
    (∑ p : (Fin 4 × Fin 4) × Fin 4,
      ‖schoberFourthV3 B₁ B₂ p‖ ^ 2) = 3 / 2 := by
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4,
        ‖schoberFourthL B₁ B₂ (i.val + j.val + k.val + 3)‖ ^ 2 /
          (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) *
            ((k.val + 1 : ℕ) : ℝ)) := by
            rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            simpa only [schoberFourthV3, Nat.cast_mul] using
              (schober_norm_div_sqrt_sq
                (schoberFourthL B₁ B₂ (i.val + j.val + k.val + 3))
                ((i.val + 1) * (j.val + 1) * (k.val + 1)) (by positivity))
    _ = _ := schoberFourthL_cubic_energy B₁ B₂

/-- The d=4 comparison-kernel energy, before division by 4!. -/
theorem schoberFourthL_quartic_energy (B₁ B₂ : ℂ) :
    (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
      ‖schoberFourthL B₁ B₂ (i.val + j.val + k.val + l.val + 4)‖ ^ 2 /
        (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) *
          ((k.val + 1 : ℕ) : ℝ) * ((l.val + 1 : ℕ) : ℝ))) =
      1 := by
  simp [Fin.sum_univ_four, schoberFourthL, norm_mul]

noncomputable def schoberFourthV4 (B₁ B₂ : ℂ)
    (p : ((Fin 4 × Fin 4) × Fin 4) × Fin 4) : ℂ :=
  schoberFourthL B₁ B₂
      (p.1.1.1.val + p.1.1.2.val + p.1.2.val + p.2.val + 4) /
    (Real.sqrt (((((p.1.1.1.val + 1) * (p.1.1.2.val + 1) *
      (p.1.2.val + 1) * (p.2.val + 1) : ℕ) : ℝ))) : ℂ)

theorem schoberFourthV4_energy (B₁ B₂ : ℂ) :
    (∑ p : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
      ‖schoberFourthV4 B₁ B₂ p‖ ^ 2) = 1 := by
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        ‖schoberFourthL B₁ B₂ (i.val + j.val + k.val + l.val + 4)‖ ^ 2 /
          (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) *
            ((k.val + 1 : ℕ) : ℝ) * ((l.val + 1 : ℕ) : ℝ)) := by
            rw [Fintype.sum_prod_type, Fintype.sum_prod_type,
              Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro l _
            simpa only [schoberFourthV4, Nat.cast_mul] using
              (schober_norm_div_sqrt_sq
                (schoberFourthL B₁ B₂
                  (i.val + j.val + k.val + l.val + 4))
                ((i.val + 1) * (j.val + 1) * (k.val + 1) * (l.val + 1))
                (by positivity))
    _ = _ := schoberFourthL_quartic_energy B₁ B₂

/-- The four finite tensor energies sum to exactly the comparison-kernel
diagonal, including the factorial weights 1/d!. -/
theorem schoberFourthL_total_energy (B₁ B₂ : ℂ) :
    (∑ i : Fin 4,
      ‖schoberFourthL B₁ B₂ (i.val + 1)‖ ^ 2 /
        ((i.val + 1 : ℕ) : ℝ)) +
      (1 / 2 : ℝ) *
        (∑ i : Fin 4, ∑ j : Fin 4,
          ‖schoberFourthL B₁ B₂ (i.val + j.val + 2)‖ ^ 2 /
            (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ))) +
      (1 / 6 : ℝ) *
        (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4,
          ‖schoberFourthL B₁ B₂ (i.val + j.val + k.val + 3)‖ ^ 2 /
            (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) *
              ((k.val + 1 : ℕ) : ℝ))) +
      (1 / 24 : ℝ) *
        (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
          ‖schoberFourthL B₁ B₂ (i.val + j.val + k.val + l.val + 4)‖ ^ 2 /
            (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) *
              ((k.val + 1 : ℕ) : ℝ) * ((l.val + 1 : ℕ) : ℝ))) =
      ‖B₂‖ ^ 2 + 4 * ‖B₁‖ ^ 2 + 1 := by
  rw [schoberFourthL_linear_energy,
    schoberFourthL_quadratic_energy,
    schoberFourthL_cubic_energy,
    schoberFourthL_quartic_energy]
  ring

/-- The four finite bilinear tensor terms of Schober's order-four kernel.
Their coefficient identity with the actual B₇ is a separate algebraic step. -/
noncomputable def schoberFourthTensorTerm1 (F : ℂ → ℂ) : ℂ :=
  let v := schoberFourthV1 (exteriorInverseCoeff F 1) (exteriorInverseCoeff F 2)
  ∑ p : Fin 4, v p * (∑ q : Fin 4, schoberActualC4 F p q * v q)

noncomputable def schoberFourthTensorTerm2 (F : ℂ → ℂ) : ℂ :=
  let v := schoberFourthV2 (exteriorInverseCoeff F 1) (exteriorInverseCoeff F 2)
  ∑ p : Fin 4 × Fin 4,
    v p * (∑ q : Fin 4 × Fin 4, schoberActualC4Tensor2 F p q * v q)

noncomputable def schoberFourthTensorTerm3 (F : ℂ → ℂ) : ℂ :=
  let v := schoberFourthV3 (exteriorInverseCoeff F 1) (exteriorInverseCoeff F 2)
  ∑ p : (Fin 4 × Fin 4) × Fin 4,
    v p * (∑ q : (Fin 4 × Fin 4) × Fin 4,
      schoberActualC4Tensor3 F p q * v q)

noncomputable def schoberFourthTensorTerm4 (F : ℂ → ℂ) : ℂ :=
  let v := schoberFourthV4 (exteriorInverseCoeff F 1) (exteriorInverseCoeff F 2)
  ∑ p : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
    v p * (∑ q : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
      schoberActualC4Tensor4 F p q * v q)

noncomputable def schoberFourthTensorPolynomial (F : ℂ → ℂ) : ℂ :=
  schoberFourthTensorTerm1 F +
    (1 / 2 : ℂ) * schoberFourthTensorTerm2 F +
    (1 / 6 : ℂ) * schoberFourthTensorTerm3 F +
    (1 / 24 : ℂ) * schoberFourthTensorTerm4 F

/-- The complete fourth-order tensor bound, with the actual inverse
coefficients and exact factorial weights. The pending algebraic bridge is
`exteriorInverseCoeff F 7 = schoberFourthTensorPolynomial F`. -/
theorem schoberFourthTensorPolynomial_norm_le_diagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖schoberFourthTensorPolynomial F‖ ≤ schoberActualDiagonal F 4 := by
  let B₁ := exteriorInverseCoeff F 1
  let B₂ := exteriorInverseCoeff F 2
  let v₁ := schoberFourthV1 B₁ B₂
  let v₂ := schoberFourthV2 B₁ B₂
  let v₃ := schoberFourthV3 B₁ B₂
  let v₄ := schoberFourthV4 B₁ B₂
  have h₁ : ‖schoberFourthTensorTerm1 F‖ ≤
      ∑ p : Fin 4, ‖v₁ p‖ ^ 2 := by
    exact schoberActualC4_bilinear_bound F hc v₁
  have h₂ : ‖schoberFourthTensorTerm2 F‖ ≤
      ∑ p : Fin 4 × Fin 4, ‖v₂ p‖ ^ 2 := by
    exact schoberActualC4Tensor2_bilinear_bound F hc v₂
  have h₃ : ‖schoberFourthTensorTerm3 F‖ ≤
      ∑ p : (Fin 4 × Fin 4) × Fin 4, ‖v₃ p‖ ^ 2 := by
    exact schoberActualC4Tensor3_bilinear_bound F hc v₃
  have h₄ : ‖schoberFourthTensorTerm4 F‖ ≤
      ∑ p : ((Fin 4 × Fin 4) × Fin 4) × Fin 4, ‖v₄ p‖ ^ 2 := by
    exact schoberActualC4Tensor4_bilinear_bound F hc v₄
  have htri : ‖schoberFourthTensorPolynomial F‖ ≤
      ‖schoberFourthTensorTerm1 F‖ +
      (1 / 2 : ℝ) * ‖schoberFourthTensorTerm2 F‖ +
      (1 / 6 : ℝ) * ‖schoberFourthTensorTerm3 F‖ +
      (1 / 24 : ℝ) * ‖schoberFourthTensorTerm4 F‖ := by
    unfold schoberFourthTensorPolynomial
    have hA := norm_add_le
      (schoberFourthTensorTerm1 F +
        (1 / 2 : ℂ) * schoberFourthTensorTerm2 F +
        (1 / 6 : ℂ) * schoberFourthTensorTerm3 F)
      ((1 / 24 : ℂ) * schoberFourthTensorTerm4 F)
    have hB := norm_add_le
      (schoberFourthTensorTerm1 F +
        (1 / 2 : ℂ) * schoberFourthTensorTerm2 F)
      ((1 / 6 : ℂ) * schoberFourthTensorTerm3 F)
    have hC := norm_add_le
      (schoberFourthTensorTerm1 F)
      ((1 / 2 : ℂ) * schoberFourthTensorTerm2 F)
    norm_num [norm_mul] at hA hB hC
    linarith
  calc
    ‖schoberFourthTensorPolynomial F‖ ≤
        ‖schoberFourthTensorTerm1 F‖ +
        (1 / 2 : ℝ) * ‖schoberFourthTensorTerm2 F‖ +
        (1 / 6 : ℝ) * ‖schoberFourthTensorTerm3 F‖ +
        (1 / 24 : ℝ) * ‖schoberFourthTensorTerm4 F‖ := htri
    _ ≤ (∑ p : Fin 4, ‖v₁ p‖ ^ 2) +
        (1 / 2 : ℝ) * (∑ p : Fin 4 × Fin 4, ‖v₂ p‖ ^ 2) +
        (1 / 6 : ℝ) * (∑ p : (Fin 4 × Fin 4) × Fin 4,
          ‖v₃ p‖ ^ 2) +
        (1 / 24 : ℝ) * (∑ p : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
          ‖v₄ p‖ ^ 2) := by
            gcongr
    _ = ‖B₂‖ ^ 2 + 4 * ‖B₁‖ ^ 2 + 1 := by
      rw [schoberFourthV1_energy, schoberFourthV2_energy,
        schoberFourthV3_energy, schoberFourthV4_energy]
      ring
    _ = schoberActualDiagonal F 4 :=
      (schoberActualDiagonal_four F hc).symm

/-- Development boundary: the analytic/tensor inequality is closed. The
remaining algebraic identification is kept explicit, never hidden in the
paper-level function class or the final theorem. -/
theorem exteriorInverseCoeff_seven_norm_le_diagonal_of_tensor_eq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hcoeff : exteriorInverseCoeff F 7 =
      schoberFourthTensorPolynomial F) :
    ‖exteriorInverseCoeff F 7‖ ≤ schoberActualDiagonal F 4 := by
  rw [hcoeff]
  exact schoberFourthTensorPolynomial_norm_le_diagonal F hc

/-- The quartic tensor term can only see the `(1,1,1,1)` mode. -/
theorem schoberFourthTensorTerm4_eq_firstCoeff_pow_four (F : ℂ → ℂ) :
    schoberFourthTensorTerm4 F = (exteriorForwardCoeff F 1) ^ 4 := by
  simp [schoberFourthTensorTerm4, schoberFourthV4, schoberFourthL,
    schoberActualC4Tensor4, schoberActualC4Tensor3,
    schoberActualC4Tensor2, schoberActualC4,
    Fintype.sum_prod_type, Fin.sum_univ_four,
    schoberBiCoeff, schoberKernelQ4_outer_one,
    schoberKernelT4Row, PowerSeries.coeff_X_pow]
  ring

private theorem schober_normalized_pair_cancel
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (x y c : ℂ) :
    (x / (Real.sqrt (m : ℝ) : ℂ)) *
      ((Real.sqrt (m : ℝ) : ℂ) *
        (Real.sqrt (n : ℝ) : ℂ) * c) *
      (y / (Real.sqrt (n : ℝ) : ℂ)) = x * c * y := by
  have hms : (Real.sqrt (m : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hm))
  have hns : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn))
  field_simp

theorem schoberFourthTensorTerm1_eq_unnormalized (F : ℂ → ℂ) :
    schoberFourthTensorTerm1 F =
      ∑ p : Fin 4, ∑ q : Fin 4,
        schoberFourthL (exteriorInverseCoeff F 1)
          (exteriorInverseCoeff F 2) (p.val + 1) *
          schoberBiCoeff (p.val + 1) (q.val + 1)
            (schoberKernelQ4
              (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
              (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
              (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
              (exteriorForwardCoeff F 7)) *
          schoberFourthL (exteriorInverseCoeff F 1)
            (exteriorInverseCoeff F 2) (q.val + 1) := by
  unfold schoberFourthTensorTerm1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simpa only [schoberFourthV1, schoberActualC4, mul_assoc] using
    (schober_normalized_pair_cancel
      (p.val + 1) (q.val + 1) (by omega) (by omega)
      (schoberFourthL (exteriorInverseCoeff F 1)
        (exteriorInverseCoeff F 2) (p.val + 1))
      (schoberFourthL (exteriorInverseCoeff F 1)
        (exteriorInverseCoeff F 2) (q.val + 1))
      (schoberBiCoeff (p.val + 1) (q.val + 1)
        (schoberKernelQ4
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7))))

theorem schoberFourthTensorTerm1_eq_forward
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberFourthTensorTerm1 F =
      exteriorForwardCoeff F 7 +
      5 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 5 +
      4 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 4 +
      (3 / 2 : ℂ) * (exteriorForwardCoeff F 3) ^ 2 +
      9 * (exteriorForwardCoeff F 1) ^ 2 * exteriorForwardCoeff F 3 +
      9 * exteriorForwardCoeff F 1 * (exteriorForwardCoeff F 2) ^ 2 +
      (9 / 4 : ℂ) * (exteriorForwardCoeff F 1) ^ 4 := by
  have h11 := (schoberKernelQ4_first_row_low
    (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
    (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
    (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
    (exteriorForwardCoeff F 7)).1
  have h21 := (schoberKernelQ4_first_row_low
    (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
    (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
    (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
    (exteriorForwardCoeff F 7)).2.1
  rw [schoberFourthTensorTerm1_eq_unnormalized,
    exteriorInverseCoeff_one_eq_forwardCoeff_one F hc,
    exteriorInverseCoeff_two_eq_forwardCoeff_two F hc]
  simp [Fin.sum_univ_four, schoberFourthL]
  simp only [h11, h21,
    schoberKernelQ4_coeff_one_two, schoberKernelQ4_coeff_two_two,
    schoberKernelQ4_coeff_one_four, schoberKernelQ4_coeff_four_one,
    schoberKernelQ4_coeff_two_four, schoberKernelQ4_coeff_four_two,
    schoberKernelQ4_coeff_four_four]
  ring

private theorem schober_sqrt_nat_mul (m n : ℕ) :
    (Real.sqrt (((m * n : ℕ) : ℝ)) : ℂ) =
      (Real.sqrt (m : ℝ) : ℂ) * (Real.sqrt (n : ℝ) : ℂ) := by
  exact_mod_cast (by
    rw [Nat.cast_mul, Real.sqrt_mul (by positivity)] :
      Real.sqrt (((m * n : ℕ) : ℝ)) =
        Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ))

private theorem schober_normalized_pair_cancel2
    (m₁ m₂ n₁ n₂ : ℕ)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (x y c₁ c₂ : ℂ) :
    (x / (Real.sqrt (((m₁ * m₂ : ℕ) : ℝ)) : ℂ)) *
      (((Real.sqrt (m₁ : ℝ) : ℂ) *
        (Real.sqrt (n₁ : ℝ) : ℂ) * c₁) *
        ((Real.sqrt (m₂ : ℝ) : ℂ) *
          (Real.sqrt (n₂ : ℝ) : ℂ) * c₂)) *
      (y / (Real.sqrt (((n₁ * n₂ : ℕ) : ℝ)) : ℂ)) =
      x * (c₁ * c₂) * y := by
  rw [schober_sqrt_nat_mul, schober_sqrt_nat_mul]
  have h₁ : (Real.sqrt (m₁ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hm₁))
  have h₂ : (Real.sqrt (m₂ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hm₂))
  have h₃ : (Real.sqrt (n₁ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn₁))
  have h₄ : (Real.sqrt (n₂ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn₂))
  field_simp

theorem schoberFourthTensorTerm2_eq_unnormalized (F : ℂ → ℂ) :
    schoberFourthTensorTerm2 F =
      ∑ p : Fin 4 × Fin 4, ∑ q : Fin 4 × Fin 4,
        schoberFourthL (exteriorInverseCoeff F 1)
          (exteriorInverseCoeff F 2) (p.1.val + p.2.val + 2) *
          (schoberBiCoeff (p.1.val + 1) (q.1.val + 1)
            (schoberKernelQ4
              (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
              (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
              (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
              (exteriorForwardCoeff F 7)) *
           schoberBiCoeff (p.2.val + 1) (q.2.val + 1)
            (schoberKernelQ4
              (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
              (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
              (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
              (exteriorForwardCoeff F 7))) *
          schoberFourthL (exteriorInverseCoeff F 1)
            (exteriorInverseCoeff F 2) (q.1.val + q.2.val + 2) := by
  unfold schoberFourthTensorTerm2
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simpa only [schoberFourthV2, schoberActualC4Tensor2,
    schoberActualC4, mul_assoc] using
    (schober_normalized_pair_cancel2
      (p.1.val + 1) (p.2.val + 1)
      (q.1.val + 1) (q.2.val + 1)
      (by omega) (by omega) (by omega) (by omega)
      (schoberFourthL (exteriorInverseCoeff F 1)
        (exteriorInverseCoeff F 2) (p.1.val + p.2.val + 2))
      (schoberFourthL (exteriorInverseCoeff F 1)
        (exteriorInverseCoeff F 2) (q.1.val + q.2.val + 2))
      (schoberBiCoeff (p.1.val + 1) (q.1.val + 1)
        (schoberKernelQ4
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7)))
      (schoberBiCoeff (p.2.val + 1) (q.2.val + 1)
        (schoberKernelQ4
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7))))

theorem schoberFourthTensorTerm2_eq_forward
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberFourthTensorTerm2 F =
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 5 +
      4 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 4 +
      3 * (exteriorForwardCoeff F 3) ^ 2 +
      11 * (exteriorForwardCoeff F 1) ^ 2 * exteriorForwardCoeff F 3 +
      10 * exteriorForwardCoeff F 1 * (exteriorForwardCoeff F 2) ^ 2 +
      (59 / 12 : ℂ) * (exteriorForwardCoeff F 1) ^ 4 := by
  have hlow := schoberKernelQ4_first_row_low
    (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
    (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
    (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
    (exteriorForwardCoeff F 7)
  rw [schoberFourthTensorTerm2_eq_unnormalized,
    exteriorInverseCoeff_one_eq_forwardCoeff_one F hc,
    exteriorInverseCoeff_two_eq_forwardCoeff_two F hc,
    Fintype.sum_prod_type]
  simp [Fintype.sum_prod_type, Fin.sum_univ_four, schoberFourthL]
  simp only [hlow.1, hlow.2.1, hlow.2.2,
    schoberKernelQ4_coeff_one_two, schoberKernelQ4_coeff_two_two,
    schoberKernelQ4_coeff_three_two, schoberKernelQ4_coeff_two_three,
    schoberKernelQ4_coeff_three_three,
    schoberKernelQ4_coeff_one_three]
  ring

private theorem schober_normalized_pair_cancel3
    (m₁ m₂ m₃ n₁ n₂ n₃ : ℕ)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hm₃ : 0 < m₃)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
    (x y c₁ c₂ c₃ : ℂ) :
    (x / (Real.sqrt (((m₁ * m₂ * m₃ : ℕ) : ℝ)) : ℂ)) *
      (((Real.sqrt (m₁ : ℝ) : ℂ) *
        (Real.sqrt (n₁ : ℝ) : ℂ) * c₁) *
        ((Real.sqrt (m₂ : ℝ) : ℂ) *
          (Real.sqrt (n₂ : ℝ) : ℂ) * c₂) *
        ((Real.sqrt (m₃ : ℝ) : ℂ) *
          (Real.sqrt (n₃ : ℝ) : ℂ) * c₃)) *
      (y / (Real.sqrt (((n₁ * n₂ * n₃ : ℕ) : ℝ)) : ℂ)) =
      x * (c₁ * c₂ * c₃) * y := by
  rw [schober_sqrt_nat_mul (m₁ * m₂) m₃,
    schober_sqrt_nat_mul m₁ m₂,
    schober_sqrt_nat_mul (n₁ * n₂) n₃,
    schober_sqrt_nat_mul n₁ n₂]
  have h₁ : (Real.sqrt (m₁ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hm₁))
  have h₂ : (Real.sqrt (m₂ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hm₂))
  have h₃ : (Real.sqrt (m₃ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hm₃))
  have h₄ : (Real.sqrt (n₁ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn₁))
  have h₅ : (Real.sqrt (n₂ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn₂))
  have h₆ : (Real.sqrt (n₃ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn₃))
  field_simp

theorem schoberFourthTensorTerm3_eq_unnormalized (F : ℂ → ℂ) :
    schoberFourthTensorTerm3 F =
      ∑ p : (Fin 4 × Fin 4) × Fin 4,
        ∑ q : (Fin 4 × Fin 4) × Fin 4,
          schoberFourthL (exteriorInverseCoeff F 1)
            (exteriorInverseCoeff F 2)
            (p.1.1.val + p.1.2.val + p.2.val + 3) *
          (schoberBiCoeff (p.1.1.val + 1) (q.1.1.val + 1)
            (schoberKernelQ4
              (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
              (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
              (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
              (exteriorForwardCoeff F 7)) *
           schoberBiCoeff (p.1.2.val + 1) (q.1.2.val + 1)
            (schoberKernelQ4
              (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
              (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
              (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
              (exteriorForwardCoeff F 7)) *
           schoberBiCoeff (p.2.val + 1) (q.2.val + 1)
            (schoberKernelQ4
              (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
              (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
              (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
              (exteriorForwardCoeff F 7))) *
          schoberFourthL (exteriorInverseCoeff F 1)
            (exteriorInverseCoeff F 2)
            (q.1.1.val + q.1.2.val + q.2.val + 3) := by
  unfold schoberFourthTensorTerm3
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simpa only [schoberFourthV3, schoberActualC4Tensor3,
    schoberActualC4Tensor2, schoberActualC4, mul_assoc] using
    (schober_normalized_pair_cancel3
      (p.1.1.val + 1) (p.1.2.val + 1) (p.2.val + 1)
      (q.1.1.val + 1) (q.1.2.val + 1) (q.2.val + 1)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
      (schoberFourthL (exteriorInverseCoeff F 1)
        (exteriorInverseCoeff F 2)
        (p.1.1.val + p.1.2.val + p.2.val + 3))
      (schoberFourthL (exteriorInverseCoeff F 1)
        (exteriorInverseCoeff F 2)
        (q.1.1.val + q.1.2.val + q.2.val + 3))
      (schoberBiCoeff (p.1.1.val + 1) (q.1.1.val + 1)
        (schoberKernelQ4
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7)))
      (schoberBiCoeff (p.1.2.val + 1) (q.1.2.val + 1)
        (schoberKernelQ4
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7)))
      (schoberBiCoeff (p.2.val + 1) (q.2.val + 1)
        (schoberKernelQ4
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7))))

theorem schoberFourthTensorTerm3_eq_forward
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberFourthTensorTerm3 F =
      3 * (exteriorForwardCoeff F 1) ^ 2 * exteriorForwardCoeff F 3 +
      6 * exteriorForwardCoeff F 1 * (exteriorForwardCoeff F 2) ^ 2 +
      (3 / 2 : ℂ) * (exteriorForwardCoeff F 1) ^ 4 := by
  have hlow := schoberKernelQ4_first_row_low
    (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
    (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
    (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
    (exteriorForwardCoeff F 7)
  rw [schoberFourthTensorTerm3_eq_unnormalized,
    exteriorInverseCoeff_one_eq_forwardCoeff_one F hc,
    exteriorInverseCoeff_two_eq_forwardCoeff_two F hc]
  simp [Fintype.sum_prod_type, Fin.sum_univ_four, schoberFourthL]
  simp only [hlow.1, hlow.2.1,
    schoberKernelQ4_coeff_one_two,
    schoberKernelQ4_coeff_two_two]
  ring

/-- The tensor exponential diagonal is exactly the seventh inverse
coefficient of the same actual exterior map. -/
theorem exteriorInverseCoeff_seven_eq_fourthTensorPolynomial
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    exteriorInverseCoeff F 7 = schoberFourthTensorPolynomial F := by
  rw [exteriorInverseCoeff_seven_eq_forward F hc]
  unfold schoberFourthTensorPolynomial
  rw [schoberFourthTensorTerm1_eq_forward F hc,
    schoberFourthTensorTerm2_eq_forward F hc,
    schoberFourthTensorTerm3_eq_forward F hc,
    schoberFourthTensorTerm4_eq_firstCoeff_pow_four F]
  ring

/-- Schober's finite fourth-order diagonal estimate for every actual
centered exterior-univalent function. -/
theorem exteriorInverseCoeff_seven_norm_le_diagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorInverseCoeff F 7‖ ≤ schoberActualDiagonal F 4 := by
  rw [exteriorInverseCoeff_seven_eq_fourthTensorPolynomial F hc]
  exact schoberFourthTensorPolynomial_norm_le_diagonal F hc

theorem exteriorInverseCoeff_seven_param_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorInverseCoeff F 7‖ ≤
      (3 + 7 * ‖exteriorForwardCoeff F 1‖ ^ 2) / 2 :=
  exteriorInverseCoeff_seven_param_le_of_diagonal F hc
    (exteriorInverseCoeff_seven_norm_le_diagonal F hc)

theorem exteriorInverseCoeff_seven_norm_le_five
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorInverseCoeff F 7‖ ≤ 5 :=
  exteriorInverseCoeff_seven_norm_le_five_of_diagonal F hc
    (exteriorInverseCoeff_seven_norm_le_diagonal F hc)

theorem exteriorInverseCoeff_seven_norm_lt_five
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hβ : ‖exteriorForwardCoeff F 1‖ < 1) :
    ‖exteriorInverseCoeff F 7‖ < 5 :=
  exteriorInverseCoeff_seven_norm_lt_five_of_diagonal F hc
    (exteriorInverseCoeff_seven_norm_le_diagonal F hc) hβ

theorem exteriorInverseCoeff_seven_norm_eq_five_iff_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    (‖exteriorInverseCoeff F 7‖ = 5 ↔
      ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :=
  exteriorInverseCoeff_seven_norm_eq_five_iff_slit_of_diagonal F hc
    (exteriorInverseCoeff_seven_norm_le_diagonal F hc)

end SpringerLean
