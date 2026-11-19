import SpringerLean.Round1813UntruncatedScalarBudget

namespace SpringerLean
set_option maxHeartbeats 500000

/-- The simpler coefficient 12 is also paid by the existing central
allowance in the truncated branch, outside the explicit tiny cutoff. -/
theorem truncated_twelve_model_cost_lt_cubic
    {m : ℕ} (hm : 1500 ≤ m) {D : ℝ}
    (hD : (3/100 : ℝ)/((m : ℝ)*Real.log (100*(m : ℝ))) ≤ D) :
    12*Real.exp (-(m : ℝ)/5)*Real.sqrt ((m : ℝ)/5)/(m : ℝ) < D^3/1000 := by
  have hm' : (1500 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hsqrt : Real.sqrt ((m : ℝ)/5) ≤ Real.sqrt (m : ℝ) :=
    Real.sqrt_le_sqrt (by linarith)
  have hcoef : (12 : ℝ)/(m : ℝ) ≤ m := by
    apply (div_le_iff₀ hm0).mpr
    nlinarith
  have hcost : 12*Real.exp (-(m : ℝ)/5)*Real.sqrt ((m : ℝ)/5)/(m : ℝ) ≤
      (m : ℝ)*Real.sqrt (m : ℝ)*(23/25 : ℝ)^m := by
    calc
      _ ≤ 12*(23/25 : ℝ)^m*Real.sqrt (m : ℝ)/(m : ℝ) := by
        gcongr <;> first | exact exp_neg_fifth_le_geometric m | exact hsqrt | linarith
      _ = (12/(m : ℝ))*(Real.sqrt (m : ℝ)*(23/25 : ℝ)^m) := by ring
      _ ≤ (m : ℝ)*(Real.sqrt (m : ℝ)*(23/25 : ℝ)^m) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by ring
  exact hcost.trans_lt (central_cost_lt_cubic_of_log_cutoff hm hD)

end SpringerLean

#print axioms SpringerLean.truncated_twelve_model_cost_lt_cubic
