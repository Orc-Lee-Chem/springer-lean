import SpringerLean.Round1785ActualAlignedNearPhaseCost

namespace SpringerLean
set_option maxHeartbeats 400000

theorem power_exp_neg_hasDerivAt (j : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => x^(j+1)*Real.exp (-x))
      (x^j*Real.exp (-x)*((j : ℝ)+1-x)) x := by
  convert (hasDerivAt_pow (j+1) x).mul (((hasDerivAt_id x).neg).exp) using 1
  · rfl
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.neg_apply, id_eq]
    rw [pow_succ]
    ring

/-- Integer power times exp(-x) decreases from its elementary mode.
This supplies both scalar monotonicities for the short model budget. -/
theorem power_exp_neg_antitone (j : ℕ) :
    AntitoneOn (fun x : ℝ => x^(j+1)*Real.exp (-x)) (Set.Ici ((j : ℝ)+1)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    (by fun_prop) (by fun_prop)
  intro x hx
  have hx' : (j : ℝ)+1 ≤ x := interior_subset hx
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hx0 : 0 ≤ x := by linarith
  rw [(power_exp_neg_hasDerivAt j x).deriv]
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (pow_nonneg hx0 _) (Real.exp_pos _).le) (sub_nonpos.mpr hx')

end SpringerLean

#print axioms SpringerLean.power_exp_neg_antitone
