import SpringerLean.Round105FourthTensorEnergy

namespace SpringerLean

/-- The exact fifth-order numerical consequence of a still-missing
fifth-order Schober diagonal comparison. The hypothesis remains explicit. -/
theorem exteriorInverseCoeff_nine_param_le_of_diagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hdiag : ‖exteriorInverseCoeff F 9‖ ≤ schoberActualDiagonal F 5) :
    ‖exteriorInverseCoeff F 9‖ ≤
      4 + 9 * ‖exteriorForwardCoeff F 1‖ ^ 2 +
        ‖exteriorForwardCoeff F 1‖ ^ 4 := by
  let β := ‖exteriorForwardCoeff F 1‖
  let B₁ := exteriorInverseCoeff F 1
  let B₂ := exteriorInverseCoeff F 2
  let B₃ := exteriorInverseCoeff F 3
  have hrow := schoberActualDiagonal_five F hc
  have harea := exteriorInverseCoeff_two_sq_area_le F hc
  have hB₃ := exteriorInverseCoeff_three_norm_le_one F hc
  have htriangle := norm_add_le B₃ (B₁ ^ 2)
  rw [norm_pow] at htriangle
  have hB₁ : ‖B₁‖ = β :=
    congrArg norm (exteriorInverseCoeff_one_eq_forwardCoeff_one F hc)
  rw [hB₁] at htriangle harea
  have hsum : ‖B₃ + B₁ ^ 2‖ ≤ 1 + β ^ 2 := by linarith
  have hsum0 : 0 ≤ ‖B₃ + B₁ ^ 2‖ := norm_nonneg _
  have hβ0 : 0 ≤ β := norm_nonneg _
  have hsumSq : ‖B₃ + B₁ ^ 2‖ ^ 2 ≤ (1 + β ^ 2) ^ 2 := by nlinarith
  rw [hrow] at hdiag
  rw [hB₁] at hdiag
  dsimp [β, B₁, B₂, B₃] at hdiag harea hsumSq ⊢
  nlinarith

/-- Conditional numerical n=5 bound, ready for an actual fifth-order
Grunsky diagonal proof. -/
theorem exteriorInverseCoeff_nine_norm_le_fourteen_of_diagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hdiag : ‖exteriorInverseCoeff F 9‖ ≤ schoberActualDiagonal F 5) :
    ‖exteriorInverseCoeff F 9‖ ≤ 14 := by
  have hβ := exteriorForwardCoeff_one_norm_le_of_finite_area F
    (fun N => exteriorForwardCoeff_finite_area F hc N)
  have hβ0 : 0 ≤ ‖exteriorForwardCoeff F 1‖ := norm_nonneg _
  have hparam := exteriorInverseCoeff_nine_param_le_of_diagonal F hc hdiag
  let β := ‖exteriorForwardCoeff F 1‖
  have hβ2 : β ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hβ0 (sub_nonneg.mpr hβ)]
  have hβ4 : β ^ 4 ≤ β ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hβ2)]
  dsimp [β] at hβ2 hβ4
  linarith

theorem exteriorInverseCoeff_nine_norm_lt_fourteen_of_diagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hdiag : ‖exteriorInverseCoeff F 9‖ ≤ schoberActualDiagonal F 5)
    (hβ : ‖exteriorForwardCoeff F 1‖ < 1) :
    ‖exteriorInverseCoeff F 9‖ < 14 := by
  let β := ‖exteriorForwardCoeff F 1‖
  have hβ0 : 0 ≤ β := norm_nonneg _
  have hβ2 : β ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hβ)
      (by positivity : 0 < 1 + β)]
  have hβ4 : β ^ 4 ≤ β ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg β) (le_of_lt (sub_pos.mpr hβ2))]
  have hparam := exteriorInverseCoeff_nine_param_le_of_diagonal F hc hdiag
  dsimp [β] at hβ2 hβ4
  linarith

/-- Both fifth-order equality directions under the one still-open actual
diagonal estimate; this is a development lemma, not a paper-level result. -/
theorem exteriorInverseCoeff_nine_norm_eq_fourteen_iff_slit_of_diagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hdiag : ‖exteriorInverseCoeff F 9‖ ≤ schoberActualDiagonal F 5) :
    (‖exteriorInverseCoeff F 9‖ = 14 ↔
      ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk) := by
  constructor
  · intro hEq
    have hβle := exteriorForwardCoeff_one_norm_le_of_finite_area F
      (fun N => exteriorForwardCoeff_finite_area F hc N)
    have hβeq : ‖exteriorForwardCoeff F 1‖ = 1 := by
      by_contra hne
      have hβlt : ‖exteriorForwardCoeff F 1‖ < 1 := lt_of_le_of_ne hβle hne
      have hstrict := exteriorInverseCoeff_nine_norm_lt_fourteen_of_diagonal
        F hc hdiag hβlt
      linarith
    have hB1 : ‖exteriorInverseCoeff F 1‖ = 1 := by
      rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc]
      exact hβeq
    exact (exteriorInverseCoeff_one_norm_eq_one_iff_slit F hc).mp hB1
  · rintro ⟨a, ha, hFG⟩
    have hcat : catalan 4 = 14 := by
      norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
    have hsharp := exteriorInverseCoeff_sharp_of_eqOn_slit_all_orders
      F hc a ha hFG 5 (by omega)
    simpa only [Nat.reduceMul, Nat.reduceSub, hcat, Nat.cast_ofNat] using hsharp

end SpringerLean
