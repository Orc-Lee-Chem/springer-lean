import SpringerLean.Round484RootOmittedSet

namespace SpringerLean
set_option Elab.async false

def parabolicStripRegion (R W : ℝ) : Set ℂ :=
  {w | w.im ^ 2 ≤ 4 * W * (W + R - w.re)}

theorem parabolicStripRegion_convex (R W : ℝ) :
    Convex ℝ (parabolicStripRegion R W) := by
  intro x hx y hy a b ha hb hab
  change x.im ^ 2 ≤ 4 * W * (W + R - x.re) at hx
  change y.im ^ 2 ≤ 4 * W * (W + R - y.re) at hy
  change (a • x + b • y).im ^ 2 ≤ 4 * W * (W + R - (a • x + b • y).re)
  simp only [Complex.add_im, Complex.add_re, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero]
  have hs : (a * x.im + b * y.im) ^ 2 ≤ a * x.im ^ 2 + b * y.im ^ 2 := by
    have hp := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x.im - y.im))
    nlinarith [hab]
  have hm := add_le_add (mul_le_mul_of_nonneg_left hx ha)
    (mul_le_mul_of_nonneg_left hy hb)
  have hid : a * (4 * W * (W + R - x.re)) + b * (4 * W * (W + R - y.re)) =
      4 * W * (W + R - (a * x.re + b * y.re)) := by
    linear_combination 4 * W * (W + R) * hab
  rw [hid] at hm
  exact hs.trans hm

theorem square_root_real_bound_implies_parabolicStrip
    {w v : ℂ} {R W : ℝ} (hW : 0 ≤ W)
    (hsquare : v ^ 2 = w - (R : ℂ)) (hv : v.re ^ 2 ≤ W) :
    w ∈ parabolicStripRegion R W := by
  have hr : v.re ^ 2 - v.im ^ 2 = w.re - R := by
    simpa [pow_two, Complex.mul_re] using congrArg Complex.re hsquare
  have hi : 2 * v.re * v.im = w.im := by
    have hit := congrArg Complex.im hsquare
    simp only [pow_two, Complex.mul_im, Complex.sub_im, Complex.ofReal_im, sub_zero] at hit
    nlinarith
  have hi2 : w.im ^ 2 = 4 * v.re ^ 2 * v.im ^ 2 := by rw [← hi]; ring
  have hd : 4 * W * (W + R - w.re) - w.im ^ 2 =
      4 * (W - v.re ^ 2) * (W + v.im ^ 2) := by
    rw [hi2]
    linear_combination 4 * W * hr
  have hp : 0 ≤ 4 * (W - v.re ^ 2) * (W + v.im ^ 2) := by positivity
  change w.im ^ 2 ≤ 4 * W * (W + R - w.re)
  linarith

/-- The convex-hull step in br:strip. Its root-support hypothesis remains
explicit until the exterior-circle support estimate is proved. -/
theorem convexHull_subset_parabolicStrip_of_root_bound
    (K : Set ℂ) {R W : ℝ} (hW : 0 ≤ W)
    (hroot : ∀ w ∈ K, ∃ v : ℂ, v ^ 2 = w - (R : ℂ) ∧ v.re ^ 2 ≤ W) :
    convexHull ℝ K ⊆ parabolicStripRegion R W := by
  apply convexHull_min _ (parabolicStripRegion_convex R W)
  intro w hw
  obtain ⟨v, hv, hvr⟩ := hroot w hw
  exact square_root_real_bound_implies_parabolicStrip hW hv hvr

end SpringerLean
