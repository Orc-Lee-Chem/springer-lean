import SpringerLean.Round1921ActualFourToSix

namespace SpringerLean

/-- The actual continuous normalized boundary-moment deficit on [6,8]. -/
theorem normalized_actual_radial_moment_six_to_eight
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    normalizedActualRadialMoment F (6 + 2 * θ) ≤
      normalizedCosineMoment (6 + 2 * θ) *
        (1 - (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 80) := by
  let D := 1 - ‖exteriorForwardCoeff F 1‖ ^ 2
  let p := 6 + 2 * θ
  obtain ⟨c, hcunit, hproj⟩ :=
    actualBoundaryProjectionSecondMoment_deficit F hc
  have hdef := normalized_even_moment_deficits F hc
  dsimp only at hdef
  rcases hdef with ⟨h4, h6, h8⟩
  have htest := actual_interpolation_deficit_from_test F hc c hcunit
    (a := 6) (by norm_num) hθ0 hθ1
  dsimp only at htest
  rw [interpolationCurvatureConstant_six] at htest
  have hx : ‖exteriorForwardCoeff F 1‖ ≤ 1 := by
    have hh := exteriorInverseCoeff_one_norm_le F hc
    rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] at hh
    exact hh
  have hD : 0 ≤ D := by
    dsimp [D]
    nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]
  have hp : 4 ≤ p := by dsimp [p]; linarith
  have hC0 := normalizedCosineMoment_nonneg p
  have hC1 := normalizedCosineMoment_le_half p (by linarith)
  have hcoef1 : 0 ≤ p * (1 - θ) / 6 := by
    apply div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hcoef2 : 0 ≤ p * θ / 8 := by
    apply div_nonneg (mul_nonneg (by linarith) hθ0) (by norm_num)
  have hκ : 0 ≤ p * θ * (1 - θ) * (13 / 168 : ℝ) := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (by linarith) hθ0
      · linarith
    · norm_num
  have h6' := mul_le_mul_of_nonneg_left h6 hcoef1
  have h8' := mul_le_mul_of_nonneg_left h8 hcoef2
  have hproj' := mul_le_mul_of_nonneg_left hproj hκ
  have hmargin := interpolation_six_to_eight_strong_margin hθ0 hθ1
  have hmargin' := mul_le_mul_of_nonneg_left hmargin
    (mul_nonneg (by linarith : 0 ≤ p) hD)
  have hmain : p * D * (1 / 640 : ℝ) ≤
      normalizedCosineMoment p - normalizedActualRadialMoment F p := by
    dsimp [p,D] at htest h6' h8' hproj' hmargin' ⊢
    nlinarith
  exact interpolation_from_bracket_to_normalized_deficit hp hD hC0 hC1
    (le_refl (1 / 640 : ℝ)) hmain

end SpringerLean

#print axioms SpringerLean.normalized_actual_radial_moment_six_to_eight
