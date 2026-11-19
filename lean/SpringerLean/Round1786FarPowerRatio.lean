import SpringerLean.Round1780AlignedStripBudget

namespace SpringerLean
set_option maxHeartbeats 500000

/-- The far aligned angular budget pays for replacing m by m-8.
Only log(1+x)<=x and log r>=1-1/r are used. -/
theorem far_power_ratio_of_angular_budget
    (N : ℕ) (hN : 1 ≤ N) {a s h : ℝ}
    (ha : 0 ≤ a) (has : a ≤ s) (hs : s < 2*(N : ℝ))
    (hcost : (2*(N : ℝ))^2*h^2/2 < 8*(s-a)) :
    (1+h^2)^N < ((2*(N : ℝ)-a)/(2*(N : ℝ)-s))^8 := by
  let m := 2*(N : ℝ)
  let r := (m-a)/(m-s)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hm : 0 < m := by dsimp [m]; positivity
  have hms : 0 < m-s := by dsimp [m]; linarith
  have hma : 0 < m-a := by linarith
  have hr : 0 < r := div_pos hma hms
  have hlog1 := Real.log_le_sub_one_of_pos (show 0 < 1+h^2 by positivity)
  have hlog2 := Real.one_sub_inv_le_log_of_pos hr
  have hratio : 1-r⁻¹=(s-a)/(m-a) := by
    dsimp [r]
    field_simp
    <;> ring
  rw [hratio] at hlog2
  have hfrac : (s-a)/m ≤ (s-a)/(m-a) :=
    div_le_div_of_nonneg_left (sub_nonneg.mpr has) hma (by linarith)
  have hlogr : (s-a)/m ≤ Real.log r := hfrac.trans hlog2
  have hlower : 8*(s-a)/m ≤ 8*Real.log r := by
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left hlogr (by norm_num : (0 : ℝ) ≤ 8)
  have hbudget : (N : ℝ)*h^2 < 8*(s-a)/m := by
    apply (lt_div_iff₀ hm).mpr
    dsimp [m] at *
    nlinarith
  change (1+h^2)^N < r^8
  apply (Real.log_lt_log_iff (pow_pos (by positivity : (0 : ℝ) < 1+h^2) N)
    (pow_pos hr 8)).mp
  rw [Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith [mul_le_mul_of_nonneg_left hlog1 hN0.le, hlower]

end SpringerLean

#print axioms SpringerLean.far_power_ratio_of_angular_budget
