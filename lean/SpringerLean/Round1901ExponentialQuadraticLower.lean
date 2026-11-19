import SpringerLean.Round1900InterpolationPowerCurvature
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace SpringerLean

/-- A short calculus proof of the Taylor lower bound needed for the
interpolation curvature estimates. The derivative of the difference is
nonnegative by 1+x ≤ exp x. -/
theorem exp_ge_one_add_self_add_half_sq {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 ≤ Real.exp x := by
  let f : ℝ → ℝ := fun t => Real.exp t - 1 - t - t ^ 2 / 2
  have hderiv (t : ℝ) : HasDerivAt f (Real.exp t - 1 - t) t := by
    have h := (((Real.hasDerivAt_exp t).sub_const 1).sub (hasDerivAt_id t)).sub
      (((hasDerivAt_id t).pow 2).div_const 2)
    have hfun : f = ((fun y : ℝ => Real.exp y - 1) - id -
        (fun y : ℝ => y ^ 2 / 2)) := by
      funext y
      rfl
    rw [hfun]
    convert h using 1
    · funext y
      rfl
    · simp only [id_eq]
      ring
  have hdiff : Differentiable ℝ f := fun t => (hderiv t).differentiableAt
  have hmono : Monotone f := monotone_of_deriv_nonneg hdiff (fun t => by
    rw [(hderiv t).deriv]
    linarith [Real.add_one_le_exp t])
  have h0 : f 0 = 0 := by simp [f]
  have hh : f 0 ≤ f x := hmono hx
  rw [h0] at hh
  dsimp [f] at hh
  linarith

end SpringerLean

#print axioms SpringerLean.exp_ge_one_add_self_add_half_sq
