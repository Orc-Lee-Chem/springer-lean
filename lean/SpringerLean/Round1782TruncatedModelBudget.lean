import SpringerLean.Round1779LogCutoffCentralBudget

namespace SpringerLean
set_option maxHeartbeats 400000

theorem exp_neg_fifth_le_geometric (m : ℕ) :
    Real.exp (-(m : ℝ)/5) ≤ (23/25 : ℝ)^m := by
  have he := Real.add_one_le_exp (1/5 : ℝ)
  have hexp : 0 < Real.exp (1/5 : ℝ) := Real.exp_pos _
  have hbase : Real.exp (-1/5 : ℝ) ≤ 23/25 := by
    rw [show (-1/5 : ℝ)=-(1/5) by ring, Real.exp_neg]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hexp).mpr
    nlinarith
  have hp := pow_le_pow_left₀ (Real.exp_pos (-1/5 : ℝ)).le hbase m
  rw [show -(m : ℝ)/5=(m : ℝ)*(-1/5) by ring, Real.exp_nat_mul]
  exact hp

/-- The truncated model cost is below the same elementary central
allowance. It needs no separate logarithmic derivative calculation. -/
theorem truncated_twoPower_model_cost_lt_cubic
    {m : ℕ} (hm : 1500 ≤ m) {D : ℝ}
    (hD : (3/100 : ℝ)/((m : ℝ)*Real.log (100*(m : ℝ))) ≤ D) :
    (54/5 : ℝ)*Real.exp (-(m : ℝ)/5)*Real.sqrt ((m : ℝ)/5)/(m : ℝ) < D^3/1000 := by
  have hm' : (1500 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hsqrt : Real.sqrt ((m : ℝ)/5) ≤ Real.sqrt (m : ℝ) :=
    Real.sqrt_le_sqrt (by linarith)
  have hcoef : (54/5 : ℝ)/(m : ℝ) ≤ m := by
    apply (div_le_iff₀ hm0).mpr
    nlinarith
  have hcost : (54/5 : ℝ)*Real.exp (-(m : ℝ)/5)*Real.sqrt ((m : ℝ)/5)/(m : ℝ) ≤
      (m : ℝ)*Real.sqrt (m : ℝ)*(23/25 : ℝ)^m := by
    calc
      _ ≤ (54/5 : ℝ)*(23/25 : ℝ)^m*Real.sqrt (m : ℝ)/(m : ℝ) := by
        gcongr <;> first | exact exp_neg_fifth_le_geometric m | exact hsqrt | linarith
      _ = ((54/5 : ℝ)/(m : ℝ))*(Real.sqrt (m : ℝ)*(23/25 : ℝ)^m) := by ring
      _ ≤ (m : ℝ)*(Real.sqrt (m : ℝ)*(23/25 : ℝ)^m) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by ring
  exact hcost.trans_lt (central_cost_lt_cubic_of_log_cutoff hm hD)

end SpringerLean

#print axioms SpringerLean.truncated_twoPower_model_cost_lt_cubic
