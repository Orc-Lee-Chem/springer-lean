import SpringerLean.Round1826AlignedReferenceCost
import SpringerLean.Round1828ActualEndpointScalarRelations
import SpringerLean.Round1822ReferenceMomentCentralMargin

namespace SpringerLean
set_option maxHeartbeats 1200000

theorem endpointPhaseBudget_add_center_neg_of_nonTiny
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (δ : ℝ)
    (hd : 0 < 2-‖P‖)
    (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hlog : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖)*Real.log (2/(2-‖P‖)) < 3/2)
    (hwidth : exteriorFineEndpointWidth P <
      (1/3 : ℝ)*(2-‖P‖)*Real.log (2/(2-‖P‖)))
    (hcutoff : (3/100 : ℝ)/(((2*k-2 : ℕ) : ℝ)*Real.log (100*((2*k-2 : ℕ) : ℝ))) ≤
      ((2*k-2 : ℕ) : ℝ)*(2-‖P‖)) :
    endpointPhaseBudget k P δ+
      (((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ))*(23/25 : ℝ)^(2*k-2) < 0 := by
  let mn := 2*k-2
  let m := (mn : ℝ)
  let D := m*(2-‖P‖)
  let a := endpointPhaseParameter k P
  have hm : 1500 ≤ mn := by dsimp [mn]; omega
  have hm0 : 0 < m := by dsimp [m]; exact_mod_cast (by omega : 0 < mn)
  have hN : 0 < m*Real.sqrt m := by positivity
  obtain ⟨_,_,ha,hau,_⟩ := endpointPhaseParameter_bounds k hk P hd ht hlog hwidth
  obtain ⟨hL,hD,hExp,hcase⟩ := endpointPhaseParameter_scalar_relations k hk P hd ht
  have hc := central_cost_lt_cubic_of_log_cutoff hm hcutoff
  have hD3 : 0 < D^3 := by dsimp [D,m,mn]; positivity
  unfold endpointPhaseBudget
  dsimp only
  by_cases halign : |(k : ℝ)*δ| ≤ Real.pi/3
  · rw [if_pos halign]
    have hmodel := alignedPhaseReferenceCost_excess_le_twelve k hk a ha hau
    have hpay : 12*Real.exp (-a)*Real.sqrt a/m < D^3/40 := by
      rcases hcase with htrunc | hfree
      · change a=m/5 at htrunc
        rw [htrunc]
        have hh := truncated_twelve_model_cost_lt_cubic hm hcutoff
        change 12*Real.exp (-m/5)*Real.sqrt (m/5)/m < D^3/1000 at hh
        rw [neg_div] at hh
        nlinarith
      · exact untruncated_twoPower_scalar_cost_lt_cubic ha hL.le hm0 hD hfree hExp
    change m*Real.sqrt m*(alignedPhaseReferenceCost k a-comparisonPositiveDiskMoment mn)-D^3/32+
      m*Real.sqrt m*(23/25 : ℝ)^mn < 0
    change m*Real.sqrt m*(23/25 : ℝ)^mn < D^3/1000 at hc
    change m*Real.sqrt m*(alignedPhaseReferenceCost k a-comparisonPositiveDiskMoment mn) ≤
      12*Real.exp (-a)*Real.sqrt a/m at hmodel
    nlinarith
  · rw [if_neg halign]
    have hh := central_allowance_lt_trueAxis_margin k hk
    have hinner : (23/25 : ℝ)^mn-comparisonPositiveDiskMoment mn/m < 0 := by
      change (23/25 : ℝ)^mn < comparisonPositiveDiskMoment mn/m at hh
      linarith
    have hneg := mul_neg_of_pos_of_neg hN hinner
    change -(m*Real.sqrt m)*comparisonPositiveDiskMoment mn/m+m*Real.sqrt m*(23/25 : ℝ)^mn < 0
    convert hneg using 1 <;> ring

end SpringerLean

#print axioms SpringerLean.endpointPhaseBudget_add_center_neg_of_nonTiny
