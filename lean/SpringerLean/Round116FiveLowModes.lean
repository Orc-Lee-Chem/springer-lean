import SpringerLean.Round115FiveCombination

namespace SpringerLean

/-- Taylor extraction of the fifth Faber combination uses the same actual
analytic factors as the Green-area estimate. -/
theorem fifthFaberCombinationFactor_actual_coeff
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (α₁ α₂ α₃ α₄ α₅ : ℂ) (k : ℕ) :
    actualTaylorCoeff
        (fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅) k =
      actualTaylorCoeff
          (fun u : ℂ =>
            u * fourthFaberCombinationFactor G α₁ α₂ α₃ α₄ u) k +
        α₅ * actualTaylorCoeff (fifthFaberFactor G) k := by
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
  have hfive : AnalyticAt ℂ (fifthFaberFactor G) 0 := by
    unfold fifthFaberFactor
    fun_prop
  let f₁ : ℂ → ℂ := fun u =>
    u * fourthFaberCombinationFactor G α₁ α₂ α₃ α₄ u
  let f₂ : ℂ → ℂ := fun u => α₅ * fifthFaberFactor G u
  calc
    _ = actualTaylorCoeff f₁ k + actualTaylorCoeff f₂ k := by
      change actualTaylorCoeff (fun u => f₁ u + f₂ u) k = _
      exact actualTaylorCoeff_add_analytic f₁ f₂
        (analyticAt_id.mul hfour) (analyticAt_const.mul hfive) k
    _ = _ := by
      simp only [f₁, f₂, actualTaylorCoeff_const_mul_analytic]

/-- The five positive Fourier modes of the combined actual Faber boundary
curve are exactly the five input coordinates, in reverse Taylor order. -/
theorem fifthFaberCombinationFactor_actual_low_coefficients
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (α₁ α₂ α₃ α₄ α₅ : ℂ) :
    actualTaylorCoeff
        (fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅) 0 = α₅ ∧
    actualTaylorCoeff
        (fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅) 1 = α₄ ∧
    actualTaylorCoeff
        (fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅) 2 = α₃ ∧
    actualTaylorCoeff
        (fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅) 3 = α₂ ∧
    actualTaylorCoeff
        (fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅) 4 = α₁ := by
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
  rcases fourthFaberCombinationFactor_actual_low_coefficients
    G hc α₁ α₂ α₃ α₄ with ⟨h40, h41, h42, h43⟩
  rcases fifthFaberFactor_actual_low_coefficients G hc with
    ⟨h50, h51, h52, h53, h54, h55⟩
  constructor
  · rw [fifthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ α₅ 0,
      actualTaylorCoeff_var_mul_zero, h50]
    ring
  constructor
  · rw [fifthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ α₅ 1,
      actualTaylorCoeff_var_mul_succ _ hfour 0, h40, h51]
    ring
  constructor
  · rw [fifthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ α₅ 2,
      actualTaylorCoeff_var_mul_succ _ hfour 1, h41, h52]
    ring
  constructor
  · rw [fifthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ α₅ 3,
      actualTaylorCoeff_var_mul_succ _ hfour 2, h42, h53]
    ring
  · rw [fifthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ α₅ 4,
      actualTaylorCoeff_var_mul_succ _ hfour 3, h43, h54]
    ring

/-- The regularized all-vector Green area inequality, with the five
positive Fourier modes replaced by their exact input coordinates. -/
theorem rescaleExterior_fifthFaber_all_vector_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ α₄ α₅ : ℂ) :
    let A := fifthFaberCombinationFactor
      (rescaleExterior s F) α₁ α₂ α₃ α₄ α₅
    ‖actualTaylorCoeff A 6‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 7‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 8‖ ^ 2 +
        4 * ‖actualTaylorCoeff A 9‖ ^ 2 +
        5 * ‖actualTaylorCoeff A 10‖ ^ 2 ≤
      ‖α₁‖ ^ 2 + 2 * ‖α₂‖ ^ 2 +
        3 * ‖α₃‖ ^ 2 + 4 * ‖α₄‖ ^ 2 +
        5 * ‖α₅‖ ^ 2 := by
  let G := rescaleExterior s F
  let A := fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  have h := fifthFaberCombination_actual_mode_energy_le
    F hc hs0 hs1 α₁ α₂ α₃ α₄ α₅
  change ‖actualTaylorCoeff A 6‖ ^ 2 +
      2 * ‖actualTaylorCoeff A 7‖ ^ 2 +
      3 * ‖actualTaylorCoeff A 8‖ ^ 2 +
      4 * ‖actualTaylorCoeff A 9‖ ^ 2 +
      5 * ‖actualTaylorCoeff A 10‖ ^ 2 ≤
    5 * ‖actualTaylorCoeff A 0‖ ^ 2 +
      4 * ‖actualTaylorCoeff A 1‖ ^ 2 +
      3 * ‖actualTaylorCoeff A 2‖ ^ 2 +
      2 * ‖actualTaylorCoeff A 3‖ ^ 2 +
      ‖actualTaylorCoeff A 4‖ ^ 2 at h
  rcases fifthFaberCombinationFactor_actual_low_coefficients
    G hcG α₁ α₂ α₃ α₄ α₅ with ⟨h0, h1, h2, h3, h4⟩
  rw [h0, h1, h2, h3, h4] at h
  convert h using 1 <;> ring

end SpringerLean
