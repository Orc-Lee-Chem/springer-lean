import SpringerLean.Round1767TwoPowerPolynomial

namespace SpringerLean

set_option maxHeartbeats 1000000

/-- A single rational induction controls the central exponential cost.
No table of orders or floating-point exponential evaluation is used. -/
theorem central_geometric_budget {m : ℕ} (hm : 1500 ≤ m) :
    (m : ℝ)^8*(23/25 : ℝ)^m < 1/8000 := by
  have hstep : (23/25 : ℝ)*(1501/1500 : ℝ)^8 < 1 := by norm_num
  induction m, hm using Nat.le_induction with
  | base =>
    have hten : (23/25 : ℝ)^10 ≤ 1/2 := by norm_num
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (23/25 : ℝ)^10) hten 150
    rw [← pow_mul] at hh
    change (23/25 : ℝ)^1500 ≤ (1/2 : ℝ)^150 at hh
    have hsmall : (1500 : ℝ)^8*(1/2 : ℝ)^150 < 1/8000 := by norm_num
    exact (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (1500 : ℝ)^8)).trans_lt hsmall
  | succ m hm ih =>
    have hm' : (1500 : ℝ) ≤ m := by exact_mod_cast hm
    have hscale : (m : ℝ)+1 ≤ (1501/1500 : ℝ)*m := by linarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (m : ℝ)+1) hscale 8
    have hpow : 0 ≤ (23/25 : ℝ)^m := by positivity
    have hN : 0 ≤ (m : ℝ)^8*(23/25 : ℝ)^m := by positivity
    calc
      ((m+1 : ℕ) : ℝ)^8*(23/25 : ℝ)^(m+1)
          ≤ ((1501/1500 : ℝ)*m)^8*((23/25 : ℝ)^m*(23/25)) := by
              rw [Nat.cast_add, Nat.cast_one, pow_succ]
              exact mul_le_mul_of_nonneg_right hp (by positivity)
      _ = ((m : ℝ)^8*(23/25 : ℝ)^m)*((23/25 : ℝ)*(1501/1500 : ℝ)^8) := by ring
      _ ≤ (m : ℝ)^8*(23/25 : ℝ)^m := by nlinarith [mul_nonneg hN (sub_nonneg.mpr hstep.le)]
      _ < 1/8000 := ih

/-- The lower deficit cutoff can be weakened to 1/(2m^2). With that
cutoff the actual central allowance is below D^3/1000, uniformly in m. -/
theorem central_cost_lt_cubic {m : ℕ} (hm : 1500 ≤ m) {D : ℝ}
    (hD : 1/(2*(m : ℝ)^2) ≤ D) :
    (m : ℝ)*Real.sqrt (m : ℝ)*(23/25 : ℝ)^m < D^3/1000 := by
  have hm' : (1500 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hsqrt : Real.sqrt (m : ℝ) ≤ m := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  have hgeo := central_geometric_budget hm
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hDscale : 1 ≤ 2*(m : ℝ)^2*D := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2*(m : ℝ)^2)).mp hD
    nlinarith
  have hcub := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hDscale 3
  have hexp : 0 ≤ (23/25 : ℝ)^m := by positivity
  have hcentr : (m : ℝ)*Real.sqrt (m : ℝ)*(23/25 : ℝ)^m ≤
      (m : ℝ)^2*(23/25 : ℝ)^m := by
    nlinarith [mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hm0.le hexp)]
  have hbound : (m : ℝ)^2*(23/25 : ℝ)^m < 1/(8000*(m : ℝ)^6) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith [hgeo]
  have hlast : 1/(8000*(m : ℝ)^6) ≤ D^3/1000 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [hcub]
  exact hcentr.trans_lt (hbound.trans_le hlast)

end SpringerLean

#print axioms SpringerLean.central_cost_lt_cubic
