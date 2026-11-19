import SpringerLean.Round1903ExponentialSquareBound

namespace SpringerLean

/-- The exact uniform curvature constant L_a from the original analytic
interpolation argument, now reduced to two elementary exponential bounds. -/
theorem interpolationCurvatureKernel_second_deriv_le
    {a k t : ℝ} (ha : 4 ≤ a) (hk : a ≤ k)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    deriv (deriv (interpolationCurvatureKernel t)) k ≤
      1 / (6 * (a - 2)) + 4 / (7 * (a - 2) ^ 2) := by
  let q := k - 2
  let r := a - 2
  let u := -Real.log t
  let v := q * u
  have hr : 0 < r := by dsimp [r]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have hqr : r ≤ q := by dsimp [q, r]; linarith
  have hu : 0 ≤ u := by
    dsimp [u]
    linarith [Real.log_nonpos ht.le ht1]
  have hv : 0 ≤ v := mul_nonneg hq.le hu
  have hcurv := curvature_exp_negative_le_one_sixth hv
  have hsq := square_exp_negative_le_four_sevenths hv
  have hformula : deriv (deriv (interpolationCurvatureKernel t)) k =
      ((v ^ 2 - 2 * v) * Real.exp (-v)) / q +
        (v ^ 2 * Real.exp (-v)) / q ^ 2 := by
    rw [interpolationCurvatureKernel_second_deriv ht,
      Real.rpow_def_of_pos ht]
    have he : Real.log t * (k - 2) = -v := by
      dsimp [v, q, u]
      ring
    rw [he]
    field_simp [ne_of_gt hq]
    dsimp [v, q, u]
    ring
  have hfirst : ((v ^ 2 - 2 * v) * Real.exp (-v)) / q ≤
      (1 / 6 : ℝ) / q := div_le_div_of_nonneg_right hcurv hq.le
  have hsecond : (v ^ 2 * Real.exp (-v)) / q ^ 2 ≤
      (4 / 7 : ℝ) / q ^ 2 :=
    div_le_div_of_nonneg_right hsq (sq_nonneg q)
  have hqinv : 1 / q ≤ 1 / r :=
    one_div_le_one_div_of_le hr hqr
  have hq2 : r ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hr.le hqr 2
  have hq2inv : 1 / q ^ 2 ≤ 1 / r ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hr) hq2
  rw [hformula]
  have hleft : (1 / 6 : ℝ) / q ≤ 1 / (6 * r) := by
    have hm := mul_le_mul_of_nonneg_left hqinv (by norm_num : (0 : ℝ) ≤ 1 / 6)
    convert hm using 1 <;> ring
  have hright : (4 / 7 : ℝ) / q ^ 2 ≤ 4 / (7 * r ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left hq2inv (by norm_num : (0 : ℝ) ≤ 4 / 7)
    convert hm using 1 <;> ring
  dsimp [r] at hleft hright
  exact add_le_add (hfirst.trans hleft) (hsecond.trans hright)

end SpringerLean

#print axioms SpringerLean.interpolationCurvatureKernel_second_deriv_le
