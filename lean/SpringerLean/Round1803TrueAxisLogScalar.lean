import SpringerLean.Round1801TrueAxisSineFloor

namespace SpringerLean
set_option maxHeartbeats 400000

/-- A single coarse sine floor pays the true-axis logarithmic cost
for 0<=s<=2; beyond that the lower power pays without phase loss. -/
theorem trueAxis_scalar_log_cost_negative
    {m s h γ θ : ℝ} (hm : 1500 ≤ m) (hs : 0 ≤ s)
    (hcost : m^2*h^2/2 ≤ 1/6+(5/8 : ℝ)*s)
    (hγlo : Real.pi/3 ≤ |γ|) (hγhi : |γ| ≤ Real.pi/2)
    (hshort : s ≤ 2 → |θ| ≤ 6/7) :
    14+m^2*h^2/2-8*s-(8/25 : ℝ)*m*(Real.sin (γ-θ))^2 < 0 := by
  have hm0 : 0 < m := by linarith
  by_cases hs2 : 2 ≤ s
  · have hpen : 0 ≤ (8/25 : ℝ)*m*(Real.sin (γ-θ))^2 := by positivity
    nlinarith
  · have hs2' : s ≤ 2 := (lt_of_not_ge hs2).le
    have hfloor := trueAxis_phase_sine_sq_floor hγlo hγhi (hshort hs2')
    have hp := mul_lt_mul_of_pos_left hfloor hm0
    nlinarith

end SpringerLean

#print axioms SpringerLean.trueAxis_scalar_log_cost_negative
