import SpringerLean.Round629SmallWidthScalar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace SpringerLean
set_option Elab.async false

noncomputable def smallWidthRadiusCeiling : ℝ :=
  1+(2/25 : ℝ)*((707107 : ℝ)/50000000)

/-- The remaining logarithmic constant after extracting log(2/d)/4.
All numerical enclosures are exact rationals proved in the fixed library. -/
theorem smallWidth_log_remainder_lt
    {r : ℝ} (hr1 : 1 ≤ r) (hr : r ≤ smallWidthRadiusCeiling) :
    Real.log ((r^2+1)/((2/25 : ℝ)*(r+1)))/2-
      Real.log 2/4-(r^2)⁻¹ < (92120 : ℝ)/1000000 := by
  let R := smallWidthRadiusCeiling
  let q := (r^2+1)/((2/25 : ℝ)*(r+1))
  let Q := (R^2+1)/((2/25 : ℝ)*(R+1))
  have hr0 : 0 < r := by linarith
  have hR1 : 1 ≤ R := by dsimp only [R,smallWidthRadiusCeiling]; norm_num
  have hR0 : 0 < R := by linarith
  have hpoly : (r^2+1)*(R+1) ≤ (R^2+1)*(r+1) := by
    have hid : (R^2+1)*(r+1)-(r^2+1)*(R+1) =
        (R-r)*(R*r+R+r-1) := by ring
    have hp : 0 ≤ (R-r)*(R*r+R+r-1) :=
      mul_nonneg (sub_nonneg.mpr hr) (by
        have hprod := mul_nonneg hR0.le hr0.le
        linarith)
    linarith
  have hq : q ≤ Q := by
    apply (div_le_div_iff₀ (by positivity : 0 < (2/25 : ℝ)*(r+1))
      (by positivity : 0 < (2/25 : ℝ)*(R+1))).mpr
    nlinarith
  have hq0 : 0 < q := by dsimp only [q]; positivity
  have hl := Real.log_le_sub_one_of_pos (div_pos hq0 (by norm_num : (0 : ℝ) < 25/2))
  rw [Real.log_div (ne_of_gt hq0) (by norm_num)] at hl
  have hlogc : Real.log (25/2 : ℝ)=2*Real.log 5-Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (25 : ℝ)=(5 : ℝ)^2 by norm_num,Real.log_pow]
    norm_num
  rw [hlogc] at hl
  have hlogq : Real.log q ≤ 2*Real.log 5-Real.log 2+Q/(25/2 : ℝ)-1 := by
    linarith
  have hsq : r^2 ≤ R^2 := (sq_le_sq₀ hr0.le hR0.le).mpr hr
  have hinv : (R^2)⁻¹ ≤ (r^2)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by positivity : 0 < r^2) hsq
  have hrat : (16094379126 : ℝ)/10000000000-
      (3/4 : ℝ)*((6931471803 : ℝ)/10000000000)+
      (Q/(25/2 : ℝ)-1)/2-(R^2)⁻¹ < (92120 : ℝ)/1000000 := by
    norm_num [Q,R,smallWidthRadiusCeiling]
  change Real.log q/2-Real.log 2/4-(r^2)⁻¹ < _
  linarith [Real.log_five_lt_d9,Real.log_two_gt_d9]

end SpringerLean
