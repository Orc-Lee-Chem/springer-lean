import SpringerLean.Round1917CosineSlitNormalization
import SpringerLean.Round1868ActualFourthMoment
import SpringerLean.Round1888StrongSixthMoment
import SpringerLean.Round1889StrongEighthMoment

namespace SpringerLean

/-- The revised four-, six-, and eight-moment deficits in the normalized
cosine scale used for continuous interpolation. -/
theorem normalized_even_moment_deficits
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    let D := 1 - ‖exteriorForwardCoeff F 1‖ ^ 2
    (3 / 16 : ℝ) * D ≤
        normalizedCosineMoment 4 - normalizedActualRadialMoment F 4 ∧
      (7 / 64 : ℝ) * D ≤
        normalizedCosineMoment 6 - normalizedActualRadialMoment F 6 ∧
      (51 / 1280 : ℝ) * D ≤
        normalizedCosineMoment 8 - normalizedActualRadialMoment F 8 := by
  have h4 := actualBoundaryRadialMoment_four_margin F hc
  have h6 := actualBoundaryRadialMoment_six_strong_margin F hc
  have h8 := actualBoundaryRadialMoment_eight_strong_margin F hc
  have hC4 := normalizedCosineMoment_eq_slit_constant 4 (by norm_num)
  have hC6 := normalizedCosineMoment_eq_slit_constant 6 (by norm_num)
  have hC8 := normalizedCosineMoment_eq_slit_constant 8 (by norm_num)
  rw [slitRadialMomentConstant_four] at hC4
  rw [slitRadialMomentConstant_six] at hC6
  rw [slitRadialMomentConstant_eight] at hC8
  norm_num at hC4 hC6 hC8
  dsimp only [normalizedActualRadialMoment]
  norm_num
  rw [hC4, hC6, hC8]
  constructor
  · linarith
  constructor
  · nlinarith [sq_nonneg (1 - ‖exteriorForwardCoeff F 1‖ ^ 2)]
  · linarith

end SpringerLean

#print axioms SpringerLean.normalized_even_moment_deficits
