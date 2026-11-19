import Mathlib.Tactic

namespace SpringerLean

/-- The active inverse radius profile is exactly inverse to the
selected-endpoint projection loss `e+5e²`. -/
theorem coarseInverseProfile_exact
    {e : ℝ} (he0 : 0 ≤ e) :
    2-(Real.sqrt (1+20*(e+5*e^2))-1)/10 = 2-e := by
  have hsq : 1+20*(e+5*e^2) = (1+10*e)^2 := by ring
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1+10*e)]
  ring

/-- The entire range needed for the first two-sided localization has
a positive square-root argument and ends at projection `31/16`. -/
theorem coarseProjectionLoss_range
    {e : ℝ} (he0 : 0 ≤ e) (heδ : e ≤ 1/20) :
    0 ≤ e+5*e^2 ∧ e+5*e^2 ≤ 1/16 := by
  constructor
  · nlinarith [sq_nonneg e]
  · nlinarith [mul_nonneg (sub_nonneg.mpr heδ) (add_nonneg he0 (by norm_num : (0:ℝ) ≤ 1/20))]

/-- The exact profile is extended linearly beyond the actual projection
range `x≤2`. Convexity of this global extension is the next input to
the finite convex-cap theorem. -/
noncomputable def coarseInverseRadius (x : ℝ) : ℝ :=
  if x ≤ 2 then
    max (39/20 : ℝ) (2-(Real.sqrt (1+20*(2-x))-1)/10)
  else x

theorem coarseInverseRadius_ge_platform_of_le_two
    {x : ℝ} (hx : x ≤ 2) :
    (39/20 : ℝ) ≤ coarseInverseRadius x := by
  simp only [coarseInverseRadius, if_pos hx]
  exact le_max_left _ _

/-- This is the exact scalar cap behind the proposed `13/n` model
cost: it retains the inverse square root instead of paying for the
weaker quadratic hinge. -/
theorem coarseInverseRadius_ge_radius
    {r x : ℝ} (hrlow : (39/20 : ℝ) ≤ r) (hrhigh : r ≤ 2)
    (hx : x ≤ r)
    (hproj : 2-x ≤ (2-r)+5*(2-r)^2) :
    r ≤ coarseInverseRadius x := by
  let e : ℝ := 2-r
  let s : ℝ := 2-x
  have he0 : 0 ≤ e := by dsimp [e]; linarith
  have hx2 : x ≤ 2 := by linarith
  have hs0 : 0 ≤ s := by dsimp [s]; linarith
  have hs : s ≤ e+5*e^2 := hproj
  have hsqarg : 0 ≤ 1+20*s := by linarith
  have hroot : Real.sqrt (1+20*s) ≤ Real.sqrt (1+20*(e+5*e^2)) := by
    exact Real.sqrt_le_sqrt (by linarith)
  have hinv := coarseInverseProfile_exact he0
  unfold coarseInverseRadius
  rw [if_pos hx2]
  apply le_max_of_le_right
  dsimp [s] at hroot
  dsimp [e] at hinv
  linarith

end SpringerLean

#print axioms SpringerLean.coarseInverseProfile_exact
#print axioms SpringerLean.coarseProjectionLoss_range
#print axioms SpringerLean.coarseInverseRadius_ge_radius
