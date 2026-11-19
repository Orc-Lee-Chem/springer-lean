import SpringerLean.Round135FiveTensorEnergy
import SpringerLean.Round75DiagonalRows

set_option maxHeartbeats 1000000

namespace SpringerLean

noncomputable def schoberFifthTensorTerm1 (F : ℂ → ℂ) : ℂ :=
  let v := schoberFifthV1 (exteriorInverseCoeff F 1)
    (exteriorInverseCoeff F 2) (exteriorInverseCoeff F 3)
  ∑ p : Fin 5, v p * (∑ q : Fin 5, schoberActualC5 F p q * v q)

noncomputable def schoberFifthTensorTerm2 (F : ℂ → ℂ) : ℂ :=
  let v := schoberFifthV2 (exteriorInverseCoeff F 1)
    (exteriorInverseCoeff F 2) (exteriorInverseCoeff F 3)
  ∑ p : Fin 5 × Fin 5, v p *
    (∑ q : Fin 5 × Fin 5, schoberActualC5Tensor2 F p q * v q)

noncomputable def schoberFifthTensorTerm3 (F : ℂ → ℂ) : ℂ :=
  let v := schoberFifthV3 (exteriorInverseCoeff F 1)
    (exteriorInverseCoeff F 2) (exteriorInverseCoeff F 3)
  ∑ p : (Fin 5 × Fin 5) × Fin 5, v p *
    (∑ q : (Fin 5 × Fin 5) × Fin 5, schoberActualC5Tensor3 F p q * v q)

noncomputable def schoberFifthTensorTerm4 (F : ℂ → ℂ) : ℂ :=
  let v := schoberFifthV4 (exteriorInverseCoeff F 1)
    (exteriorInverseCoeff F 2) (exteriorInverseCoeff F 3)
  ∑ p : ((Fin 5 × Fin 5) × Fin 5) × Fin 5, v p *
    (∑ q : ((Fin 5 × Fin 5) × Fin 5) × Fin 5,
      schoberActualC5Tensor4 F p q * v q)

noncomputable def schoberFifthTensorTerm5 (F : ℂ → ℂ) : ℂ :=
  let v := schoberFifthV5 (exteriorInverseCoeff F 1)
    (exteriorInverseCoeff F 2) (exteriorInverseCoeff F 3)
  ∑ p : (((Fin 5 × Fin 5) × Fin 5) × Fin 5) × Fin 5, v p *
    (∑ q : (((Fin 5 × Fin 5) × Fin 5) × Fin 5) × Fin 5,
      schoberActualC5Tensor5 F p q * v q)

noncomputable def schoberFifthTensorPolynomial (F : ℂ → ℂ) : ℂ :=
  schoberFifthTensorTerm1 F +
    (1 / 2 : ℂ) * schoberFifthTensorTerm2 F +
    (1 / 6 : ℂ) * schoberFifthTensorTerm3 F +
    (1 / 24 : ℂ) * schoberFifthTensorTerm4 F +
    (1 / 120 : ℂ) * schoberFifthTensorTerm5 F

theorem schoberFifthTensorPolynomial_norm_le_diagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖schoberFifthTensorPolynomial F‖ ≤ schoberActualDiagonal F 5 := by
  let B₁ := exteriorInverseCoeff F 1
  let B₂ := exteriorInverseCoeff F 2
  let B₃ := exteriorInverseCoeff F 3
  let v₁ := schoberFifthV1 B₁ B₂ B₃
  let v₂ := schoberFifthV2 B₁ B₂ B₃
  let v₃ := schoberFifthV3 B₁ B₂ B₃
  let v₄ := schoberFifthV4 B₁ B₂ B₃
  let v₅ := schoberFifthV5 B₁ B₂ B₃
  have h₁ : ‖schoberFifthTensorTerm1 F‖ ≤
      ∑ p : Fin 5, ‖v₁ p‖ ^ 2 :=
    schoberActualC5_bilinear_bound F hc v₁
  have h₂ : ‖schoberFifthTensorTerm2 F‖ ≤
      ∑ p : Fin 5 × Fin 5, ‖v₂ p‖ ^ 2 :=
    schoberActualC5Tensor2_bilinear_bound F hc v₂
  have h₃ : ‖schoberFifthTensorTerm3 F‖ ≤
      ∑ p : (Fin 5 × Fin 5) × Fin 5, ‖v₃ p‖ ^ 2 :=
    schoberActualC5Tensor3_bilinear_bound F hc v₃
  have h₄ : ‖schoberFifthTensorTerm4 F‖ ≤
      ∑ p : ((Fin 5 × Fin 5) × Fin 5) × Fin 5, ‖v₄ p‖ ^ 2 :=
    schoberActualC5Tensor4_bilinear_bound F hc v₄
  have h₅ : ‖schoberFifthTensorTerm5 F‖ ≤
      ∑ p : (((Fin 5 × Fin 5) × Fin 5) × Fin 5) × Fin 5,
        ‖v₅ p‖ ^ 2 :=
    schoberActualC5Tensor5_bilinear_bound F hc v₅
  have htri : ‖schoberFifthTensorPolynomial F‖ ≤
      ‖schoberFifthTensorTerm1 F‖ +
      (1 / 2 : ℝ) * ‖schoberFifthTensorTerm2 F‖ +
      (1 / 6 : ℝ) * ‖schoberFifthTensorTerm3 F‖ +
      (1 / 24 : ℝ) * ‖schoberFifthTensorTerm4 F‖ +
      (1 / 120 : ℝ) * ‖schoberFifthTensorTerm5 F‖ := by
    unfold schoberFifthTensorPolynomial
    have hA := norm_add_le
      (schoberFifthTensorTerm1 F +
        (1 / 2 : ℂ) * schoberFifthTensorTerm2 F +
        (1 / 6 : ℂ) * schoberFifthTensorTerm3 F +
        (1 / 24 : ℂ) * schoberFifthTensorTerm4 F)
      ((1 / 120 : ℂ) * schoberFifthTensorTerm5 F)
    have hB := norm_add_le
      (schoberFifthTensorTerm1 F +
        (1 / 2 : ℂ) * schoberFifthTensorTerm2 F +
        (1 / 6 : ℂ) * schoberFifthTensorTerm3 F)
      ((1 / 24 : ℂ) * schoberFifthTensorTerm4 F)
    have hC := norm_add_le
      (schoberFifthTensorTerm1 F +
        (1 / 2 : ℂ) * schoberFifthTensorTerm2 F)
      ((1 / 6 : ℂ) * schoberFifthTensorTerm3 F)
    have hD := norm_add_le (schoberFifthTensorTerm1 F)
      ((1 / 2 : ℂ) * schoberFifthTensorTerm2 F)
    norm_num [norm_mul] at hA hB hC hD
    linarith
  calc
    ‖schoberFifthTensorPolynomial F‖ ≤
        ‖schoberFifthTensorTerm1 F‖ +
        (1 / 2 : ℝ) * ‖schoberFifthTensorTerm2 F‖ +
        (1 / 6 : ℝ) * ‖schoberFifthTensorTerm3 F‖ +
        (1 / 24 : ℝ) * ‖schoberFifthTensorTerm4 F‖ +
        (1 / 120 : ℝ) * ‖schoberFifthTensorTerm5 F‖ := htri
    _ ≤ (∑ p : Fin 5, ‖v₁ p‖ ^ 2) +
        (1 / 2 : ℝ) * (∑ p : Fin 5 × Fin 5, ‖v₂ p‖ ^ 2) +
        (1 / 6 : ℝ) * (∑ p : (Fin 5 × Fin 5) × Fin 5,
          ‖v₃ p‖ ^ 2) +
        (1 / 24 : ℝ) * (∑ p : ((Fin 5 × Fin 5) × Fin 5) × Fin 5,
          ‖v₄ p‖ ^ 2) +
        (1 / 120 : ℝ) *
          (∑ p : (((Fin 5 × Fin 5) × Fin 5) × Fin 5) × Fin 5,
            ‖v₅ p‖ ^ 2) := by gcongr
    _ = ‖B₃ + B₁ ^ 2‖ ^ 2 + 4 * ‖B₂‖ ^ 2 +
          9 * ‖B₁‖ ^ 2 + 1 := by
      rw [schoberFifthV1_energy, schoberFifthV2_energy,
        schoberFifthV3_energy, schoberFifthV4_energy,
        schoberFifthV5_energy]
      simpa only [mul_one] using
        schoberFifthL_total_energy_arithmetic B₁ B₂ B₃
    _ = schoberActualDiagonal F 5 :=
      (schoberActualDiagonal_five F hc).symm

theorem exteriorInverseCoeff_nine_norm_le_diagonal_of_tensor_eq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hcoeff : exteriorInverseCoeff F 9 = schoberFifthTensorPolynomial F) :
    ‖exteriorInverseCoeff F 9‖ ≤ schoberActualDiagonal F 5 := by
  rw [hcoeff]
  exact schoberFifthTensorPolynomial_norm_le_diagonal F hc

end SpringerLean
