import SpringerLean.Round1785ActualAlignedNearPhaseCost

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 700000

def trueAxisMomentRatioLambda (m : ℝ) : ℝ :=
  ((m-1)/m)*∏ j ∈ Finset.range 4, (m-(2*(j : ℝ)+1))/(m-2*(j : ℝ)+2)

/-- One common logarithmic bound for the four moment-ratio factors.
The weaker constant 14 avoids the optimized decimal 13.1. -/
theorem trueAxisMomentRatioLambda_pos_and_log {m : ℝ} (hm : 1500 ≤ m) :
    0 < trueAxisMomentRatioLambda m ∧ -14 < m*Real.log (trueAxisMomentRatioLambda m) := by
  let f : ℕ → ℝ := fun j => (m-(2*(j : ℝ)+1))/(m-2*(j : ℝ)+2)
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m-1 := by linarith
  have hm7 : 0 < m-7 := by linarith
  have hidx {j : ℕ} (hj : j ∈ Finset.range 4) : (j : ℝ) ≤ 3 := by
    exact_mod_cast (by simp only [Finset.mem_range] at hj; omega : j ≤ 3)
  have hfpos (j : ℕ) (hj : j ∈ Finset.range 4) : 0 < f j := by
    have hh := hidx hj
    dsimp [f]
    exact div_pos (by linarith) (by linarith)
  have hflog (j : ℕ) (hj : j ∈ Finset.range 4) : -3/(m-7) ≤ Real.log (f j) := by
    have hj' := hidx hj
    have hnum : 0 < m-(2*(j : ℝ)+1) := by linarith
    have hden : 0 < m-2*(j : ℝ)+2 := by linarith
    have hh := Real.one_sub_inv_le_log_of_pos (hfpos j hj)
    have heq : 1-(f j)⁻¹= -3/(m-(2*(j : ℝ)+1)) := by
      dsimp [f]
      field_simp
      <;> ring
    rw [heq] at hh
    have hfrac := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) hm7
      (show m-7 ≤ m-(2*(j : ℝ)+1) by linarith)
    have hneg : -3/(m-7) ≤ -3/(m-(2*(j : ℝ)+1)) := by
      simpa only [neg_div] using neg_le_neg hfrac
    exact hneg.trans hh
  have hfirst : -1/(m-7) ≤ Real.log ((m-1)/m) := by
    have hh := Real.one_sub_inv_le_log_of_pos (div_pos hm1 hm0)
    have heq : 1-((m-1)/m)⁻¹= -1/(m-1) := by field_simp <;> ring
    rw [heq] at hh
    have hfrac := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hm7
      (show m-7 ≤ m-1 by linarith)
    have hneg : -1/(m-7) ≤ -1/(m-1) := by simpa only [neg_div] using neg_le_neg hfrac
    exact hneg.trans hh
  have hp : 0 < ∏ j ∈ Finset.range 4, f j := Finset.prod_pos hfpos
  have hLambda : 0 < trueAxisMomentRatioLambda m := mul_pos (div_pos hm1 hm0) hp
  have hsum := Finset.sum_le_sum hflog
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat] at hsum
  have hlog : -13/(m-7) ≤ Real.log (trueAxisMomentRatioLambda m) := by
    change -13/(m-7) ≤ Real.log (((m-1)/m)*(∏ j ∈ Finset.range 4, f j))
    rw [Real.log_mul (div_pos hm1 hm0).ne' hp.ne', Real.log_prod (fun j hj => (hfpos j hj).ne')]
    have hh := add_le_add hfirst hsum
    have heq : -1/(m-7)+4*(-3/(m-7))= -13/(m-7) := by ring
    rw [heq] at hh
    exact hh
  have hstrict : -14 < m*(-13/(m-7)) := by
    rw [←mul_div_assoc]
    apply (lt_div_iff₀ hm7).mpr
    linarith
  exact ⟨hLambda, hstrict.trans_le (mul_le_mul_of_nonneg_left hlog hm0.le)⟩

end
end SpringerLean

#print axioms SpringerLean.trueAxisMomentRatioLambda_pos_and_log
