import SpringerLean.Round146SixLowModes
import SpringerLean.Round116FiveLowModes

namespace SpringerLean

/-- The sixth combination's actual Taylor coefficients split into the
shifted first five rows and the sixth Faber row. -/
theorem sixthFaberCombinationFactor_actual_coeff
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (α₁ α₂ α₃ α₄ α₅ α₆ : ℂ) (k : ℕ) :
    actualTaylorCoeff
        (sixthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅ α₆) k =
      actualTaylorCoeff (fun u : ℂ =>
          u * fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅ u) k +
        α₆ * actualTaylorCoeff (sixthFaberFactor G) k := by
  have hφ : AnalyticAt ℂ (exteriorPhi G) 0 :=
    exteriorPhi_analyticAt G hc.2.2
  have hthree : AnalyticAt ℂ
      (thirdFaberCombinationFactor G α₁ α₂ α₃) 0 := by
    unfold thirdFaberCombinationFactor
    fun_prop
  have hfourthFactor : AnalyticAt ℂ (fourthFaberFactor G) 0 := by
    unfold fourthFaberFactor
    fun_prop
  have hfour : AnalyticAt ℂ
      (fourthFaberCombinationFactor G α₁ α₂ α₃ α₄) 0 := by
    change AnalyticAt ℂ (fun u : ℂ =>
      u * thirdFaberCombinationFactor G α₁ α₂ α₃ u +
      α₄ * fourthFaberFactor G u) 0
    exact (analyticAt_id.mul hthree).add
      (analyticAt_const.mul hfourthFactor)
  have hfifthFactor : AnalyticAt ℂ (fifthFaberFactor G) 0 := by
    unfold fifthFaberFactor
    fun_prop
  have hfive : AnalyticAt ℂ
      (fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅) 0 := by
    change AnalyticAt ℂ (fun u : ℂ =>
      u * fourthFaberCombinationFactor G α₁ α₂ α₃ α₄ u +
      α₅ * fifthFaberFactor G u) 0
    exact (analyticAt_id.mul hfour).add
      (analyticAt_const.mul hfifthFactor)
  have hsix : AnalyticAt ℂ (sixthFaberFactor G) 0 := by
    unfold sixthFaberFactor
    fun_prop
  let f₁ : ℂ → ℂ := fun u =>
    u * fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅ u
  let f₂ : ℂ → ℂ := fun u => α₆ * sixthFaberFactor G u
  calc
    _ = actualTaylorCoeff f₁ k + actualTaylorCoeff f₂ k := by
      change actualTaylorCoeff (fun u => f₁ u + f₂ u) k = _
      exact actualTaylorCoeff_add_analytic f₁ f₂
        (analyticAt_id.mul hfive) (analyticAt_const.mul hsix) k
    _ = _ := by
      simp only [f₁, f₂, actualTaylorCoeff_const_mul_analytic]

/-- The six nonnegative Fourier modes of the common boundary factor are
exactly the six freely chosen complex test weights. -/
theorem sixthFaberCombinationFactor_actual_low_coefficients
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (α₁ α₂ α₃ α₄ α₅ α₆ : ℂ) :
    actualTaylorCoeff
        (sixthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅ α₆) 0 = α₆ ∧
    actualTaylorCoeff
        (sixthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅ α₆) 1 = α₅ ∧
    actualTaylorCoeff
        (sixthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅ α₆) 2 = α₄ ∧
    actualTaylorCoeff
        (sixthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅ α₆) 3 = α₃ ∧
    actualTaylorCoeff
        (sixthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅ α₆) 4 = α₂ ∧
    actualTaylorCoeff
        (sixthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅ α₆) 5 = α₁ := by
  have hφ : AnalyticAt ℂ (exteriorPhi G) 0 :=
    exteriorPhi_analyticAt G hc.2.2
  have hfive : AnalyticAt ℂ
      (fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅) 0 := by
    unfold fifthFaberCombinationFactor fourthFaberCombinationFactor
      thirdFaberCombinationFactor fifthFaberFactor fourthFaberFactor
    fun_prop
  rcases fifthFaberCombinationFactor_actual_low_coefficients
    G hc α₁ α₂ α₃ α₄ α₅ with ⟨h50, h51, h52, h53, h54⟩
  rcases sixthFaberFactor_actual_low_coefficients G hc with
    ⟨h60, h61, h62, h63, h64, h65, h66⟩
  constructor
  · rw [sixthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ α₅ α₆ 0,
      actualTaylorCoeff_var_mul_zero, h60]
    ring
  constructor
  · rw [sixthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ α₅ α₆ 1,
      actualTaylorCoeff_var_mul_succ _ hfive 0, h50, h61]
    ring
  constructor
  · rw [sixthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ α₅ α₆ 2,
      actualTaylorCoeff_var_mul_succ _ hfive 1, h51, h62]
    ring
  constructor
  · rw [sixthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ α₅ α₆ 3,
      actualTaylorCoeff_var_mul_succ _ hfive 2, h52, h63]
    ring
  constructor
  · rw [sixthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ α₅ α₆ 4,
      actualTaylorCoeff_var_mul_succ _ hfive 3, h53, h64]
    ring
  · rw [sixthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ α₅ α₆ 5,
      actualTaylorCoeff_var_mul_succ _ hfive 4, h54, h65]
    ring

/-- Actual positive-mode normalization turns the signed area statement
into a weighted six-vector inequality, still at a regularization `s<1`. -/
theorem rescaleExterior_sixthFaber_all_vector_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ α₄ α₅ α₆ : ℂ) :
    let A := sixthFaberCombinationFactor
      (rescaleExterior s F) α₁ α₂ α₃ α₄ α₅ α₆
    ‖actualTaylorCoeff A 7‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 8‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 9‖ ^ 2 +
        4 * ‖actualTaylorCoeff A 10‖ ^ 2 +
        5 * ‖actualTaylorCoeff A 11‖ ^ 2 +
        6 * ‖actualTaylorCoeff A 12‖ ^ 2 ≤
      ‖α₁‖ ^ 2 + 2 * ‖α₂‖ ^ 2 +
        3 * ‖α₃‖ ^ 2 + 4 * ‖α₄‖ ^ 2 +
        5 * ‖α₅‖ ^ 2 + 6 * ‖α₆‖ ^ 2 := by
  let G := rescaleExterior s F
  let A := sixthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅ α₆
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  have h := sixthFaberCombination_actual_mode_energy_le
    F hc hs0 hs1 α₁ α₂ α₃ α₄ α₅ α₆
  change ‖actualTaylorCoeff A 7‖ ^ 2 +
      2 * ‖actualTaylorCoeff A 8‖ ^ 2 +
      3 * ‖actualTaylorCoeff A 9‖ ^ 2 +
      4 * ‖actualTaylorCoeff A 10‖ ^ 2 +
      5 * ‖actualTaylorCoeff A 11‖ ^ 2 +
      6 * ‖actualTaylorCoeff A 12‖ ^ 2 ≤
    6 * ‖actualTaylorCoeff A 0‖ ^ 2 +
      5 * ‖actualTaylorCoeff A 1‖ ^ 2 +
      4 * ‖actualTaylorCoeff A 2‖ ^ 2 +
      3 * ‖actualTaylorCoeff A 3‖ ^ 2 +
      2 * ‖actualTaylorCoeff A 4‖ ^ 2 +
      ‖actualTaylorCoeff A 5‖ ^ 2 at h
  rcases sixthFaberCombinationFactor_actual_low_coefficients
    G hcG α₁ α₂ α₃ α₄ α₅ α₆ with ⟨h0, h1, h2, h3, h4, h5⟩
  rw [h0, h1, h2, h3, h4, h5] at h
  convert h using 1 <;> ring

end SpringerLean
