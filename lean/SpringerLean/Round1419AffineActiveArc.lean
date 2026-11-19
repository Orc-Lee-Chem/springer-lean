import SpringerLean.Round1416RefinedAffineConvex

namespace SpringerLean

/-- The refined affine branch has a convenient dilation form for the
angle-to-angle substitution used in its circle cost. -/
theorem refinedAffine_branch_dilation
    (W s : ℝ) :
    2-(1-(107/100 : ℝ)*W)*s+(107/100 : ℝ)*W^2 =
      (1+(107/200 : ℝ)*W^2)*
        (2-((1-(107/100 : ℝ)*W)/(1+(107/200 : ℝ)*W^2))*s) := by
  have hA : 1+(107/200 : ℝ)*W^2 ≠ 0 := by positivity
  field_simp [hA]
  ring

/-- The nonplateau part can only occur in a short angular window,
because the affine branch has already fallen below 1.9 at s=0.102. -/
theorem refinedAffine_active_s_lt_51_500
    {W s : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/100)
    (hactive : (19/10 : ℝ) <
      2-(1-(107/100 : ℝ)*W)*s+(107/100 : ℝ)*W^2) :
    s < (51/500 : ℝ) := by
  by_contra h
  have hs : (51/500 : ℝ) ≤ s := le_of_not_gt h
  have hSlope : 0 ≤ 1-(107/100 : ℝ)*W := by linarith
  have hmult := mul_nonneg (sub_nonneg.mpr hs) hSlope
  have hWsq : W^2 ≤ W/100 := by
    have hh := mul_nonneg hW0 (sub_nonneg.mpr hW)
    nlinarith
  nlinarith [hmult,hWsq]

/-- At a nonnegative squared strip width, the dilation factor is in
the unit interval. -/
theorem refinedAffine_gamma_pos_le_one
    {W : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/100) :
    0 < (1-(107/100 : ℝ)*W)/(1+(107/200 : ℝ)*W^2) ∧
      (1-(107/100 : ℝ)*W)/(1+(107/200 : ℝ)*W^2) ≤ 1 := by
  have hA : 0 < 1+(107/200 : ℝ)*W^2 := by positivity
  constructor
  · exact div_pos (by linarith) hA
  · apply (div_le_one hA).mpr
    nlinarith [sq_nonneg W]

end SpringerLean

#print axioms SpringerLean.refinedAffine_branch_dilation
#print axioms SpringerLean.refinedAffine_active_s_lt_51_500
#print axioms SpringerLean.refinedAffine_gamma_pos_le_one
