import SpringerLean.Round1781AlignedRayTrigonometry

namespace SpringerLean
set_option maxHeartbeats 700000

theorem rotated_strip_deficit_le
    {R p q x C S τ : ℝ} (hR : R ≤ 2) (hx : 0 ≤ x)
    (hC0 : 0 < C) (hC1 : C ≤ 1) (hτ : C*τ=|S|)
    (hrot : x=C*p+S*q) : R-p ≤ 2-x+|q| * τ := by
  have hprod : S*q ≤ |S| * |q| := by
    calc
      S*q ≤ |S*q| := le_abs_self _
      _ = |S| * |q| := abs_mul _ _
  have hRx := mul_le_mul_of_nonneg_left hR hC0.le
  have hxC := mul_le_mul_of_nonneg_right hC1 hx
  apply (mul_le_mul_iff_left₀ hC0).mp
  rw [←hτ] at hprod
  nlinarith

theorem rotated_strip_scaled_quadratic
    {m W R p q x C S τ : ℝ} (hm : 0 ≤ m) (hW : 0 ≤ W)
    (hR : R ≤ 2) (hx : 0 ≤ x) (hC0 : 0 < C) (hC1 : C ≤ 1)
    (hτ : C*τ=|S|) (hrot : x=C*p+S*q)
    (hstrip : q^2 ≤ 4*W*(W+R-p)) :
    (m*|q|)^2 ≤ 4*(m*W)*(m*W+2*(m*(1-x/2))+(m*|q|)*τ) := by
  have hd := rotated_strip_deficit_le hR hx hC0 hC1 hτ hrot
  have hmd := mul_le_mul_of_nonneg_left hd hm
  have hup := mul_le_mul_of_nonneg_left hmd
    (show 0 ≤ 4*m*W by positivity)
  rw [← sq_abs q] at hstrip
  have hs := mul_le_mul_of_nonneg_left hstrip (sq_nonneg m)
  nlinarith

theorem rotated_strip_scaled_slope
    {m p q x Y C S τ : ℝ} (hm : 0 ≤ m) (hx : 0 < x)
    (hC0 : 0 < C) (hunit : C^2+S^2=1) (hτ : C*τ=|S|)
    (hrot : x=C*p+S*q) (hrotY : Y=C*q-S*p)
    (hmt : m*τ ≤ 21/10) (hxC : 7/4 ≤ x*C) :
    m*|Y|/x ≤ 21/10+(4/7 : ℝ)*(m*|q|) := by
  have hY : C*Y=q-S*x := by
    rw [hrotY, hrot]
    have hh := congrArg (fun z : ℝ => z*q) hunit
    nlinarith
  have hab : |q-S*x| ≤ |q|+|S*x| := by
    simpa only [abs_neg, sub_eq_add_neg] using (abs_add_le q (-(S*x)))
  rw [←hY, abs_mul, abs_of_pos hC0, abs_mul, abs_of_pos hx, ←hτ] at hab
  have hh := mul_le_mul_of_nonneg_left hab hm
  have hQ0 : 0 ≤ m*|q| := mul_nonneg hm (abs_nonneg q)
  have hQ := mul_le_mul_of_nonneg_left hxC hQ0
  have ht := mul_le_mul_of_nonneg_left hmt (mul_nonneg hx.le hC0.le)
  apply (div_le_iff₀ hx).mpr
  apply (mul_le_mul_iff_left₀ hC0).mp
  nlinarith

end SpringerLean

#print axioms SpringerLean.rotated_strip_scaled_quadratic
#print axioms SpringerLean.rotated_strip_scaled_slope
