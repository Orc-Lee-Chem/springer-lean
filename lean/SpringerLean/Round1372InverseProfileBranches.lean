import SpringerLean.Round1361ExactInverseConvex

namespace SpringerLean

/-- The exact convex profile changes from platform to active branch at
`x=31/16`, corresponding to radial deficit `1/20`. -/
theorem coarseInverseRadius_at_threshold :
    coarseInverseRadius (31/16 : ℝ) = 39/20 := by
  have hx : (31/16 : ℝ) ≤ 2 := by norm_num
  have harg : 1+20*(2-(31/16 : ℝ)) = (3/2 : ℝ)^2 := by norm_num
  simp only [coarseInverseRadius, if_pos hx]
  rw [harg, Real.sqrt_sq_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<3/2)]
  norm_num

theorem coarseInverseRadius_eq_platform_of_le_threshold
    {x : ℝ} (hx : x ≤ 31/16) :
    coarseInverseRadius x = 39/20 := by
  have hle := coarseInverseRadius_mono hx
  rw [coarseInverseRadius_at_threshold] at hle
  have hge := coarseInverseRadius_ge_platform x
  exact le_antisymm hle hge

theorem coarseInverseRadius_at_two : coarseInverseRadius 2 = 2 := by
  have hx : (2:ℝ) ≤ 2 := le_rfl
  simp [coarseInverseRadius, hx, max_eq_right (by norm_num : (39/20:ℝ) ≤ 2)]

theorem coarseInverseRadius_eq_active
    {x : ℝ} (hxlo : (31/16 : ℝ) ≤ x) (hxhi : x ≤ 2) :
    coarseInverseRadius x =
      2-(Real.sqrt (1+20*(2-x))-1)/10 := by
  have harg : 1+20*(2-x) ≤ (3/2 : ℝ)^2 := by
    nlinarith
  have hroot : Real.sqrt (1+20*(2-x)) ≤ 3/2 := by
    have hs := Real.sqrt_le_sqrt harg
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<3/2)] using hs
  have hplatform : (39/20 : ℝ) ≤
      2-(Real.sqrt (1+20*(2-x))-1)/10 := by
    linarith
  simp [coarseInverseRadius, hxhi, max_eq_right hplatform]

/-- Exact active change of variables for the circle-cost integral. -/
theorem coarseInverseRadius_on_projection_loss
    {e : ℝ} (he0 : 0 ≤ e) (heδ : e ≤ 1/20) :
    coarseInverseRadius (2-(e+5*e^2)) = 2-e := by
  obtain ⟨hs0,hsδ⟩ := coarseProjectionLoss_range he0 heδ
  have hxlo : (31/16 : ℝ) ≤ 2-(e+5*e^2) := by linarith
  have hxhi : 2-(e+5*e^2) ≤ 2 := by linarith
  rw [coarseInverseRadius_eq_active hxlo hxhi]
  convert coarseInverseProfile_exact he0 using 1 <;> ring

end SpringerLean

#print axioms SpringerLean.coarseInverseRadius_at_threshold
#print axioms SpringerLean.coarseInverseRadius_eq_platform_of_le_threshold
#print axioms SpringerLean.coarseInverseRadius_eq_active
#print axioms SpringerLean.coarseInverseRadius_on_projection_loss
