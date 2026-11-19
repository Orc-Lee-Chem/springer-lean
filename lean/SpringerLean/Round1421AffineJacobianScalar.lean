import SpringerLean.Round1420AffineWidthWindow

namespace SpringerLean
set_option maxHeartbeats 200000

/-- The normalized affine dilation differs from one by at most
`1.07107 W` in the localized width window. -/
theorem refinedAffine_one_sub_gamma_le
    {W : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500) :
    1-(1-(107/100:ℝ)*W)/(1+(107/200:ℝ)*W^2) ≤
      (107107/100000:ℝ)*W := by
  let u : ℝ := 1+(107/200:ℝ)*W^2
  let v : ℝ := 1-(107/100:ℝ)*W
  have hu : 0 < u := by dsimp [u]; positivity
  have huone : 1 ≤ u := by dsimp [u]; nlinarith [sq_nonneg W]
  have huv : 0 ≤ u-v := by dsimp [u,v]; nlinarith [sq_nonneg W]
  have hfrac : (u-v)/u ≤ u-v := by
    apply (div_le_iff₀ hu).2
    nlinarith [mul_nonneg huv (sub_nonneg.mpr huone)]
  have hsmall : W^2 ≤ W/500 := by
    nlinarith [mul_nonneg hW0 (sub_nonneg.mpr hW)]
  have hbound : u-v ≤ (107107/100000:ℝ)*W := by
    dsimp [u,v]
    nlinarith
  have heq : 1-v/u=(u-v)/u := by field_simp
  change 1-v/u ≤ _
  rw [heq]
  exact hfrac.trans hbound

/-- Pointwise square-root Jacobian factor on the whole active arc.
The angular derivative also contains the separate factor `γ⁻¹ᐟ²`. -/
theorem refinedAffine_jacobian_sqrt_le
    {W s γ : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hs0 : 0 ≤ s) (hs : s ≤ 51/500)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hγ : 1-γ ≤ (107107/100000:ℝ)*W) :
    Real.sqrt ((4-γ*s)/(4-s)) ≤ 1+(71/5000:ℝ)*W := by
  have hden : 0 < 4-s := by linarith
  have hnum : 0 ≤ 4-γ*s := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hγ1) hs0]
  have hleft : (1-γ)*s ≤ (107107/100000:ℝ)*W*(51/500:ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hγ hs0
    have hs' := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ (107107/100000:ℝ)*W by positivity)
    nlinarith
  have hright : (2*(71/5000:ℝ)*W)*(1949/500:ℝ) ≤
      (2*(71/5000:ℝ)*W)*(4-s) := by
    have hs' : (1949/500:ℝ) ≤ 4-s := by linarith
    exact mul_le_mul_of_nonneg_left hs' (by positivity)
  have hcore : (1-γ)*s ≤ (2*(71/5000:ℝ)*W)*(4-s) := by
    have hcoef : (107107/100000:ℝ)*(51/500) <
      2*(71/5000)*(1949/500) := by norm_num
    nlinarith [mul_nonneg hW0 (sub_nonneg.mpr hcoef.le)]
  have hratio : (4-γ*s)/(4-s) ≤ (1+(71/5000:ℝ)*W)^2 := by
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg ((71/5000:ℝ)*W)]
  have hsqrtSq := Real.sq_sqrt (div_nonneg hnum hden.le)
  have hsqrt0 : 0 ≤ Real.sqrt ((4-γ*s)/(4-s)) := Real.sqrt_nonneg _
  nlinarith

end SpringerLean

#print axioms SpringerLean.refinedAffine_one_sub_gamma_le
#print axioms SpringerLean.refinedAffine_jacobian_sqrt_le
