import SpringerLean.Round1802PowerExpAntitone

namespace SpringerLean
set_option maxHeartbeats 600000

theorem power_exp_neg_rate_hasDerivAt (j : ℕ) (rate x : ℝ) :
    HasDerivAt (fun x : ℝ => x^(j+1)*Real.exp (-rate*x))
      (x^j*Real.exp (-rate*x)*((j : ℝ)+1-rate*x)) x := by
  convert (hasDerivAt_pow (j+1) x).mul
    ((((hasDerivAt_id x).const_mul (-rate))).exp) using 1
  · rfl
  · simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,id_eq]
    rw [pow_succ]
    ring

/-- The central tiny-deficit ratio is controlled without an implicit
root: its logarithmic variable has this elementary monotonicity. -/
theorem power_exp_neg_rate_antitone (j : ℕ) {rate : ℝ} (hrate : 0 < rate) :
    AntitoneOn (fun x : ℝ => x^(j+1)*Real.exp (-rate*x))
      (Set.Ici (((j : ℝ)+1)/rate)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) (by fun_prop) (by fun_prop)
  intro x hx
  have hx' : ((j : ℝ)+1)/rate ≤ x := interior_subset hx
  have hx0 : 0 ≤ x := (div_nonneg (by positivity) hrate.le).trans hx'
  have hprod : (j : ℝ)+1 ≤ rate*x := by
    have hh := (div_le_iff₀ hrate).mp hx'
    nlinarith
  rw [(power_exp_neg_rate_hasDerivAt j rate x).deriv]
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (pow_nonneg hx0 _) (Real.exp_pos _).le) (sub_nonpos.mpr hprod)

end SpringerLean

#print axioms SpringerLean.power_exp_neg_rate_antitone
