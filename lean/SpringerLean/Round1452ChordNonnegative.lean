import SpringerLean.Round1451MovingSaving0067

namespace SpringerLean

theorem refinedAffineRadius_mono
    {W x y : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hxy : x ≤ y) :
    refinedAffineRadius W x ≤ refinedAffineRadius W y := by
  have hv : 0 ≤ refinedAffineV W := by
    dsimp [refinedAffineV]
    nlinarith
  unfold refinedAffineRadius
  apply max_le_max le_rfl
  nlinarith [mul_nonneg hv (sub_nonneg.mpr hxy)]

theorem refinedAffineChordPower_nonneg
    (W : ℝ) (n : ℕ) (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    {x₀ μ x : ℝ} (hμ : x₀ < μ) :
    0 ≤ refinedAffineChordPower W n x₀ μ x := by
  by_cases hx : x ≤ x₀
  · simp only [refinedAffineChordPower,if_pos hx]
    exact pow_nonneg (refinedAffineRadius_pos W x).le _
  · have hgap : 0 ≤ refinedAffineRadius W μ^n -
        refinedAffineRadius W x₀^n := by
      exact sub_nonneg.mpr
        (pow_le_pow_left₀ (refinedAffineRadius_pos W x₀).le
          (refinedAffineRadius_mono hW0 hW hμ.le) n)
    have hquot : 0 ≤ (x-x₀)/(μ-x₀) := by
      apply div_nonneg
      · exact sub_nonneg.mpr (le_of_lt (lt_of_not_ge hx))
      · exact (sub_pos.mpr hμ).le
    simp only [refinedAffineChordPower,if_neg hx]
    exact add_nonneg
      (pow_nonneg (refinedAffineRadius_pos W x₀).le _)
      (mul_nonneg hquot hgap)

end SpringerLean

#print axioms SpringerLean.refinedAffineRadius_mono
#print axioms SpringerLean.refinedAffineChordPower_nonneg
