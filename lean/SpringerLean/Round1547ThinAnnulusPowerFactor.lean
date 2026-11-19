import SpringerLean.Round1546ThinAnnulusRadialMass

namespace SpringerLean
set_option maxHeartbeats 640000

/-- On the outer annulus the peak deficit retains at least 90% of d,
and the comparison radius stays above 99/100. -/
theorem thinAnnulus_peak_parameter_bounds
    {m : ℕ} (hm : 1500 ≤ m) {d r : ℝ}
    (hd0 : 0 < d) (hD : (m:ℝ)*d ≤ 3/20)
    (hrband : 1-Real.sqrt d/16 ≤ r) (hr1 : r ≤ 1) :
    let v := d-(3/2:ℝ)*(1-r)*Real.sqrt d
    (9/10:ℝ)*d ≤ v ∧ v ≤ d ∧ (99/100:ℝ) ≤ r := by
  dsimp only
  have hmR : (1500:ℝ) ≤ m := by exact_mod_cast hm
  have hs0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hs2 : (Real.sqrt d)^2=d := Real.sq_sqrt hd0.le
  have hdsmall : d ≤ 1/1500 := by
    have hp := mul_nonneg (sub_nonneg.mpr hmR) hd0.le
    nlinarith [hD,hp]
  have hsmax : Real.sqrt d ≤ 3/100 := by nlinarith [hs2]
  have hmul := mul_le_mul_of_nonneg_right hrband hs0
  have hpos : 0 ≤ (1-r)*Real.sqrt d := by positivity
  constructor
  · nlinarith [hmul,hs2]
  constructor
  · nlinarith [hpos]
  · nlinarith [hrband,hsmax]

/-- The binomial lower bound suffices for the actual md<3/20 range;
the costly exponential 0.51 estimate is unnecessary here. -/
theorem thinAnnulus_power_factor_gt_nine_tenths
    {m : ℕ} (hm : 1500 ≤ m) {d r : ℝ}
    (hd0 : 0 < d) (hD : (m:ℝ)*d ≤ 3/20)
    (hrband : 1-Real.sqrt d/16 ≤ r) (hr1 : r ≤ 1) :
    let v := d-(3/2:ℝ)*(1-r)*Real.sqrt d
    (9/10:ℝ) < (1-v/(2*r))^(m-2) := by
  dsimp only
  let v : ℝ := d-(3/2:ℝ)*(1-r)*Real.sqrt d
  have hb := thinAnnulus_peak_parameter_bounds hm hd0 hD hrband hr1
  dsimp only at hb
  have hv0 : 0 ≤ v := by dsimp [v]; nlinarith [hb.1,hd0]
  have hvle : v ≤ d := hb.2.1
  have hrmin : (99/100:ℝ) ≤ r := hb.2.2
  have hr0 : 0 < r := by linarith
  have hmR : (1500:ℝ) ≤ m := by exact_mod_cast hm
  have hm2 : 2 ≤ m := by omega
  have hdelta : v/(2*r) < 1/10 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*r)).2
    nlinarith [hD,hrmin,hmR,hd0,hvle]
  have ha0 : 0 ≤ 1-v/(2*r) := by linarith
  have hBern := one_add_mul_sub_le_pow
    (show (-1:ℝ) ≤ 1-v/(2*r) by linarith) (m-2)
  have hmSub : ((m-2:ℕ):ℝ) = (m:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ m)]
    norm_num
  have hmult : ((m-2:ℕ):ℝ)*v ≤ (m:ℝ)*d := by
    rw [hmSub]
    have hmvd := mul_le_mul_of_nonneg_left hvle
      (show 0 ≤ (m:ℝ)-2 by linarith)
    have htwo : 0 ≤ 2*d := by positivity
    nlinarith [hmvd]
  have hratio : ((m-2:ℕ):ℝ)*(v/(2*r)) ≤
      ((m:ℝ)*d)/(2*r) := by
    have h := div_le_div_of_nonneg_right hmult
      (by positivity : 0 ≤ 2*r)
    convert h using 1 <;> ring
  have hDsmall : ((m:ℝ)*d)/(2*r) < 1/10 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*r)).2
    nlinarith [hD,hrmin]
  have hBern' : 1-((m-2:ℕ):ℝ)*(v/(2*r)) ≤
      (1-v/(2*r))^(m-2) := by
    convert hBern using 1 <;> ring
  dsimp [v] at *
  nlinarith [hBern',hratio,hDsmall]

end SpringerLean

#print axioms SpringerLean.thinAnnulus_peak_parameter_bounds
#print axioms SpringerLean.thinAnnulus_power_factor_gt_nine_tenths
