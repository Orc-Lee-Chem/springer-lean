import SpringerLean.Round1902ExponentialCurvatureBound

namespace SpringerLean

theorem exp_ge_cubic {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
  let f : ℝ → ℝ := fun t => Real.exp t - 1 - t - t ^ 2 / 2 - t ^ 3 / 6
  have hderiv (t : ℝ) : HasDerivAt f (Real.exp t - 1 - t - t ^ 2 / 2) t := by
    have h := (((((Real.hasDerivAt_exp t).sub_const 1).sub
      (hasDerivAt_id t)).sub (((hasDerivAt_id t).pow 2).div_const 2)).sub
      (((hasDerivAt_id t).pow 3).div_const 6))
    have hfun : f = ((fun y : ℝ => Real.exp y - 1) - id -
        (fun y : ℝ => y ^ 2 / 2) - (fun y : ℝ => y ^ 3 / 6)) := by
      funext y
      rfl
    rw [hfun]
    convert h using 1
    · funext y
      rfl
    · simp only [id_eq]
      ring
  have hdiff : Differentiable ℝ f := fun t => (hderiv t).differentiableAt
  have hmono : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
      hdiff.differentiableOn (fun t ht => by
        rw [(hderiv t).deriv]
        have ht0 : 0 ≤ t := by
          have : t ∈ Set.Ioi (0 : ℝ) := by simpa only [interior_Ici] using ht
          exact this.le
        linarith [exp_ge_one_add_self_add_half_sq ht0])
  have h0 : f 0 = 0 := by simp [f]
  have hh : f 0 ≤ f x := hmono (by simp) hx hx
  rw [h0] at hh
  dsimp [f] at hh
  linarith

/-- The second elementary bound used in the interpolation curvature
constant: v² exp(-v) ≤ 4/7 for v≥0. -/
theorem square_exp_negative_le_four_sevenths
    {v : ℝ} (hv : 0 ≤ v) :
    v ^ 2 * Real.exp (-v) ≤ 4 / 7 := by
  have hmain : (7 / 4 : ℝ) * v ^ 2 ≤ Real.exp v := by
    by_cases hv1 : v ≤ 1
    · have hq := exp_ge_one_add_self_add_half_sq hv
      nlinarith [mul_nonneg hv (sub_nonneg.mpr hv1)]
    · by_cases hv2 : v ≤ 2
      · let u := v - 1
        have hu0 : 0 ≤ u := by dsimp [u]; linarith
        have hu1 : u ≤ 1 := by dsimp [u]; linarith
        have hc := exp_ge_cubic hu0
        have he : (2718 / 1000 : ℝ) < Real.exp 1 :=
          lt_trans (by norm_num) Real.exp_one_gt_d9
        have hbase : 0 ≤ 1 + u + u ^ 2 / 2 + u ^ 3 / 6 := by positivity
        have hproduct : (2718 / 1000 : ℝ) *
            (1 + u + u ^ 2 / 2 + u ^ 3 / 6) ≤ Real.exp v := by
          have heq : v = 1 + u := by dsimp [u]; ring
          rw [heq, Real.exp_add]
          calc
            _ ≤ Real.exp 1 * (1 + u + u ^ 2 / 2 + u ^ 3 / 6) :=
              mul_le_mul_of_nonneg_right he.le hbase
            _ ≤ Real.exp 1 * Real.exp u :=
              mul_le_mul_of_nonneg_left hc (Real.exp_pos 1).le
        by_cases hu : u ≤ 3 / 4
        · have hsmall : 0 ≤ (1 - u) * u :=
            mul_nonneg (by linarith) hu0
          have hsq : 0 ≤ u ^ 2 := sq_nonneg u
          dsimp [u] at *
          nlinarith [mul_nonneg (by linarith : 0 ≤ 3 / 4 - (v - 1)) hsq]
        · have hcub : (3 / 4 : ℝ) * u ^ 2 ≤ u ^ 3 := by
            nlinarith [mul_nonneg (by linarith : 0 ≤ u - 3 / 4) (sq_nonneg u)]
          dsimp [u] at *
          nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - (v - 1))
            (sq_nonneg (v - 1))]
      · let u := v - 2
        have hu0 : 0 ≤ u := by dsimp [u]; linarith
        have hq := exp_ge_one_add_self_add_half_sq hu0
        have he : (7 : ℝ) < Real.exp 2 :=
          lt_trans (by norm_num) exp_two_gt_twenty_two_thirds
        have hbase : 0 ≤ 1 + u + u ^ 2 / 2 := by positivity
        have hproduct : (7 : ℝ) * (1 + u + u ^ 2 / 2) ≤ Real.exp v := by
          have heq : v = 2 + u := by dsimp [u]; ring
          rw [heq, Real.exp_add]
          calc
            _ ≤ Real.exp 2 * (1 + u + u ^ 2 / 2) :=
              mul_le_mul_of_nonneg_right he.le hbase
            _ ≤ Real.exp 2 * Real.exp u :=
              mul_le_mul_of_nonneg_left hq (Real.exp_pos 2).le
        dsimp [u] at *
        nlinarith [sq_nonneg (v - 2)]
  have hm := mul_le_mul_of_nonneg_right hmain (Real.exp_nonneg (-v))
  rw [← Real.exp_add] at hm
  have heq : v + -v = 0 := by ring
  rw [heq, Real.exp_zero] at hm
  nlinarith

end SpringerLean

#print axioms SpringerLean.square_exp_negative_le_four_sevenths
