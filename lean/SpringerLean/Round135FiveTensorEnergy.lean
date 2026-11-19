import SpringerLean.Round133FiveTensorContraction
import SpringerLean.Round134FifthVectorEnergy

set_option maxHeartbeats 1000000

namespace SpringerLean

private theorem fifth_norm_div_sqrt_sq (z : ℂ) (m : ℕ) (hm : 0 < m) :
    ‖z / (Real.sqrt (m : ℝ) : ℂ)‖ ^ 2 = ‖z‖ ^ 2 / (m : ℝ) := by
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]

noncomputable def schoberFifthV1 (B₁ B₂ B₃ : ℂ) (i : Fin 5) : ℂ :=
  schoberFifthL B₁ B₂ B₃ (i.val + 1) /
    (Real.sqrt ((i.val + 1 : ℕ) : ℝ) : ℂ)

noncomputable def schoberFifthV2 (B₁ B₂ B₃ : ℂ)
    (p : Fin 5 × Fin 5) : ℂ :=
  schoberFifthL B₁ B₂ B₃ (p.1.val + p.2.val + 2) /
    (Real.sqrt ((((p.1.val + 1) * (p.2.val + 1) : ℕ) : ℝ)) : ℂ)

noncomputable def schoberFifthV3 (B₁ B₂ B₃ : ℂ)
    (p : (Fin 5 × Fin 5) × Fin 5) : ℂ :=
  schoberFifthL B₁ B₂ B₃
      (p.1.1.val + p.1.2.val + p.2.val + 3) /
    (Real.sqrt (((((p.1.1.val + 1) * (p.1.2.val + 1) *
      (p.2.val + 1) : ℕ) : ℝ))) : ℂ)

noncomputable def schoberFifthV4 (B₁ B₂ B₃ : ℂ)
    (p : ((Fin 5 × Fin 5) × Fin 5) × Fin 5) : ℂ :=
  schoberFifthL B₁ B₂ B₃
      (p.1.1.1.val + p.1.1.2.val + p.1.2.val + p.2.val + 4) /
    (Real.sqrt (((((p.1.1.1.val + 1) * (p.1.1.2.val + 1) *
      (p.1.2.val + 1) * (p.2.val + 1) : ℕ) : ℝ))) : ℂ)

noncomputable def schoberFifthV5 (B₁ B₂ B₃ : ℂ)
    (p : (((Fin 5 × Fin 5) × Fin 5) × Fin 5) × Fin 5) : ℂ :=
  schoberFifthL B₁ B₂ B₃
      (p.1.1.1.1.val + p.1.1.1.2.val + p.1.1.2.val +
        p.1.2.val + p.2.val + 5) /
    (Real.sqrt (((((p.1.1.1.1.val + 1) * (p.1.1.1.2.val + 1) *
      (p.1.1.2.val + 1) * (p.1.2.val + 1) *
      (p.2.val + 1) : ℕ) : ℝ))) : ℂ)

theorem schoberFifthV1_energy (B₁ B₂ B₃ : ℂ) :
    (∑ i : Fin 5, ‖schoberFifthV1 B₁ B₂ B₃ i‖ ^ 2) =
      ‖B₃ + B₁ ^ 2‖ ^ 2 + 2 * ‖B₂‖ ^ 2 +
        3 * ‖B₁‖ ^ 2 + 1 / 5 := by
  calc
    _ = ∑ i : Fin 5,
        ‖schoberFifthL B₁ B₂ B₃ (i.val + 1)‖ ^ 2 /
          ((i.val + 1 : ℕ) : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            exact fifth_norm_div_sqrt_sq _ _ (by omega)
    _ = _ := schoberFifthL_linear_energy B₁ B₂ B₃

theorem schoberFifthV2_energy (B₁ B₂ B₃ : ℂ) :
    (∑ p : Fin 5 × Fin 5, ‖schoberFifthV2 B₁ B₂ B₃ p‖ ^ 2) =
      4 * ‖B₂‖ ^ 2 + 9 * ‖B₁‖ ^ 2 + 5 / 6 := by
  calc
    _ = ∑ i : Fin 5, ∑ j : Fin 5,
        ‖schoberFifthL B₁ B₂ B₃ (i.val + j.val + 2)‖ ^ 2 /
          (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ)) := by
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            simpa only [schoberFifthV2, Nat.cast_mul] using
              (fifth_norm_div_sqrt_sq
                (schoberFifthL B₁ B₂ B₃ (i.val + j.val + 2))
                ((i.val + 1) * (j.val + 1)) (by positivity))
    _ = _ := schoberFifthL_quadratic_energy B₁ B₂ B₃

theorem schoberFifthV3_energy (B₁ B₂ B₃ : ℂ) :
    (∑ p : (Fin 5 × Fin 5) × Fin 5,
      ‖schoberFifthV3 B₁ B₂ B₃ p‖ ^ 2) =
      9 * ‖B₁‖ ^ 2 + 7 / 4 := by
  calc
    _ = ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5,
        ‖schoberFifthL B₁ B₂ B₃
            (i.val + j.val + k.val + 3)‖ ^ 2 /
          (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) *
            ((k.val + 1 : ℕ) : ℝ)) := by
            rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            simpa only [schoberFifthV3, Nat.cast_mul] using
              (fifth_norm_div_sqrt_sq
                (schoberFifthL B₁ B₂ B₃ (i.val + j.val + k.val + 3))
                ((i.val + 1) * (j.val + 1) * (k.val + 1))
                (by positivity))
    _ = _ := schoberFifthL_cubic_energy B₁ B₂ B₃

theorem schoberFifthV4_energy (B₁ B₂ B₃ : ℂ) :
    (∑ p : ((Fin 5 × Fin 5) × Fin 5) × Fin 5,
      ‖schoberFifthV4 B₁ B₂ B₃ p‖ ^ 2) = 2 := by
  calc
    _ = ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5,
        ‖schoberFifthL B₁ B₂ B₃
            (i.val + j.val + k.val + l.val + 4)‖ ^ 2 /
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
            simpa only [schoberFifthV4, Nat.cast_mul] using
              (fifth_norm_div_sqrt_sq
                (schoberFifthL B₁ B₂ B₃
                  (i.val + j.val + k.val + l.val + 4))
                ((i.val + 1) * (j.val + 1) * (k.val + 1) *
                  (l.val + 1)) (by positivity))
    _ = _ := schoberFifthL_quartic_energy B₁ B₂ B₃

theorem schoberFifthV5_energy (B₁ B₂ B₃ : ℂ) :
    (∑ p : (((Fin 5 × Fin 5) × Fin 5) × Fin 5) × Fin 5,
      ‖schoberFifthV5 B₁ B₂ B₃ p‖ ^ 2) = 1 := by
  calc
    _ = ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5,
        ∑ l : Fin 5, ∑ m : Fin 5,
        ‖schoberFifthL B₁ B₂ B₃
            (i.val + j.val + k.val + l.val + m.val + 5)‖ ^ 2 /
          (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) *
            ((k.val + 1 : ℕ) : ℝ) * ((l.val + 1 : ℕ) : ℝ) *
            ((m.val + 1 : ℕ) : ℝ)) := by
            rw [Fintype.sum_prod_type, Fintype.sum_prod_type,
              Fintype.sum_prod_type, Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro l _
            apply Finset.sum_congr rfl
            intro m _
            simpa only [schoberFifthV5, Nat.cast_mul] using
              (fifth_norm_div_sqrt_sq
                (schoberFifthL B₁ B₂ B₃
                  (i.val + j.val + k.val + l.val + m.val + 5))
                ((i.val + 1) * (j.val + 1) * (k.val + 1) *
                  (l.val + 1) * (m.val + 1)) (by positivity))
    _ = _ := schoberFifthL_quintic_energy B₁ B₂ B₃

end SpringerLean
