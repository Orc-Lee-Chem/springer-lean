import SpringerLean.Round1404MediumWidthEstimate

namespace SpringerLean
set_option Elab.async false

/-- A coarse bound for the localized logarithmic deficit. It is ample
for the affine strip cap and avoids differentiating `d log(2/d)`. -/
theorem localized_deficit_log_product_lt_one_hundred
    {d : ℝ} (hd0 : 0 < d) (hd : d ≤ (1/1501 : ℝ)) :
    d * Real.log (2/d) < (1/100 : ℝ) := by
  let u : ℝ := 1501*d
  have hu0 : 0 < u := by dsimp [u]; nlinarith
  have hune : u ≠ 0 := ne_of_gt hu0
  have hu : u ≤ 1 := by dsimp [u]; nlinarith
  have hratio : (2 : ℝ)/d = 3002/u := by
    dsimp [u]
    field_simp [ne_of_gt hd0]
    ring
  have hlogratio : Real.log (2/d)=Real.log 3002-Real.log u := by
    rw [hratio,Real.log_div (by norm_num) hune]
  have hlogu : -Real.log u ≤ 1/u-1 := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1/u by positivity)
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hune] at h
    norm_num at h
    simp only [one_div]
    linarith
  have hlog : Real.log (2/d) ≤ Real.log 3002+1/u-1 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog hd0.le
  have hdu : d*(1/u)=1/1501 := by
    dsimp [u]
    field_simp [ne_of_gt hd0]
  have hlog3002pos : 0 ≤ Real.log (3002 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  have hlog3002 : Real.log (3002 : ℝ) < 9 := by
    have h := Real.log_le_log
      (by norm_num : (0 : ℝ) < 3002)
      (by norm_num : (3002 : ℝ) ≤ 4096)
    rw [show (4096 : ℝ)=2^12 by norm_num,Real.log_pow] at h
    have htwo : Real.log (2 : ℝ) < 3/4 := by
      linarith [Real.log_two_lt_d9]
    have hnum : (12:ℝ)*Real.log 2 < 9 := by nlinarith
    exact lt_of_le_of_lt (by simpa only [Nat.cast_ofNat] using h) hnum
  have hprod := mul_le_mul_of_nonneg_right hd hlog3002pos
  have hbound : d*Real.log (2/d) ≤
      d*Real.log 3002 + 1/1501-d := by
    nlinarith [hmul,hdu]
  nlinarith [hprod]

/-- The actual strip radius from the medium-width estimate is below
one hundredth in the entire localized deficit interval. -/
theorem mediumWidth_sq_lt_one_hundred
    {d : ℝ} (hd0 : 0 < d) (hd : d ≤ (1/1501 : ℝ)) :
    (exteriorRealRootWidth (2-d) (1+Real.sqrt d/10))^2 <
      (1/100 : ℝ) := by
  have hW := mediumWidth_exact_width_sq_lt hd0 hd
  have hlog := localized_deficit_log_product_lt_one_hundred hd0 hd
  nlinarith

end SpringerLean

#print axioms SpringerLean.localized_deficit_log_product_lt_one_hundred
#print axioms SpringerLean.mediumWidth_sq_lt_one_hundred
