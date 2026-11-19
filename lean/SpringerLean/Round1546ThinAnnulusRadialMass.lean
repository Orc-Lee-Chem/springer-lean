import SpringerLean.Round1545ThinAnnulusExponentialChord

namespace SpringerLean
set_option maxHeartbeats 640000

private theorem thinAnnulus_radial_exponent_lower
    {m : ℕ} (hm : 1500 ≤ m) {d : ℝ} (hd0 : 0 < d) :
    (9/4:ℝ)*Real.sqrt ((m:ℝ)*d) ≤
      (m:ℝ)*Real.sqrt d/16 := by
  have hmR : (1500:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) ≤ m := by positivity
  have hs0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hD0 : 0 ≤ Real.sqrt ((m:ℝ)*d) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt d)^2=d := Real.sq_sqrt hd0.le
  have hD2 : (Real.sqrt ((m:ℝ)*d))^2=(m:ℝ)*d :=
    Real.sq_sqrt (mul_nonneg hm0 hd0.le)
  have hmDiff : 0 ≤ (m:ℝ)-1296 := by linarith
  have hprod : 0 ≤ ((m:ℝ)-1296)*(m:ℝ)*d := by positivity
  have hsquare : ((9/4:ℝ)*Real.sqrt ((m:ℝ)*d))^2 ≤
      ((m:ℝ)*Real.sqrt d/16)^2 := by
    nlinarith [hprod,hs2,hD2]
  have hright0 : 0 ≤ (m:ℝ)*Real.sqrt d/16 := by positivity
  have hleft0 : 0 ≤ (9/4:ℝ)*Real.sqrt ((m:ℝ)*d) := by positivity
  nlinarith [hsquare]

private theorem thinAnnulus_power_le_exp
    {m : ℕ} (hm : 1500 ≤ m) {d : ℝ}
    (hd0 : 0 < d) (hD : (m:ℝ)*d ≤ 1) :
    (1-Real.sqrt d/16)^m ≤
      Real.exp (-(9/4)*Real.sqrt ((m:ℝ)*d)) := by
  have hmR : (1500:ℝ) ≤ m := by exact_mod_cast hm
  have hd1 : d ≤ 1 := by nlinarith [hD,hd0]
  have hs0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hs2 : (Real.sqrt d)^2=d := Real.sq_sqrt hd0.le
  have hs1 : Real.sqrt d ≤ 1 := by nlinarith [hs2,hd1]
  have hbase0 : 0 ≤ 1-Real.sqrt d/16 := by linarith
  have hbase : 1-Real.sqrt d/16 ≤ Real.exp (-Real.sqrt d/16) := by
    linarith [Real.add_one_le_exp (-Real.sqrt d/16)]
  have hpow := pow_le_pow_left₀ hbase0 hbase m
  rw [←Real.exp_nat_mul] at hpow
  have harg : (m:ℝ)*(-Real.sqrt d/16) =
      -(m:ℝ)*Real.sqrt d/16 := by ring
  rw [harg] at hpow
  have hlow := thinAnnulus_radial_exponent_lower hm hd0
  have hexp : Real.exp (-(m:ℝ)*Real.sqrt d/16) ≤
      Real.exp (-(9/4)*Real.sqrt ((m:ℝ)*d)) :=
    Real.exp_monotone (by linarith [hlow])
  exact hpow.trans hexp

/-- A uniform radial mass estimate for every m≥1500 and 0<md≤1. -/
theorem thinAnnulus_radial_mass_general
    {m : ℕ} (hm : 1500 ≤ m) {d : ℝ}
    (hd0 : 0 < d) (hD : (m:ℝ)*d ≤ 1) :
    (8/9:ℝ)*Real.sqrt ((m:ℝ)*d) ≤
      1-(1-Real.sqrt d/16)^m := by
  have hmR : (0:ℝ) ≤ m := by positivity
  have hD0 : 0 ≤ (m:ℝ)*d := mul_nonneg hmR hd0.le
  have hx0 : 0 ≤ Real.sqrt ((m:ℝ)*d) := Real.sqrt_nonneg _
  have hx1 : Real.sqrt ((m:ℝ)*d) ≤ 1 := by
    nlinarith [Real.sq_sqrt hD0]
  have hchord := thinAnnulus_exp_loss_general hx0 hx1
  have hpow := thinAnnulus_power_le_exp hm hd0 hD
  linarith

/-- At the actual endpoint scale md<3/20, the radial mass improves to
4sqrt(md)/3. -/
theorem thinAnnulus_radial_mass_small
    {m : ℕ} (hm : 1500 ≤ m) {d : ℝ}
    (hd0 : 0 < d) (hD : (m:ℝ)*d ≤ 3/20) :
    (4/3:ℝ)*Real.sqrt ((m:ℝ)*d) ≤
      1-(1-Real.sqrt d/16)^m := by
  have hmR : (0:ℝ) ≤ m := by positivity
  have hD0 : 0 ≤ (m:ℝ)*d := mul_nonneg hmR hd0.le
  have hx0 : 0 ≤ Real.sqrt ((m:ℝ)*d) := Real.sqrt_nonneg _
  have hx2 : Real.sqrt ((m:ℝ)*d) ≤ 2/5 := by
    nlinarith [Real.sq_sqrt hD0]
  have hchord := thinAnnulus_exp_loss_small hx0 hx2
  have hpow := thinAnnulus_power_le_exp hm hd0 (by linarith [hD])
  linarith

end SpringerLean

#print axioms SpringerLean.thinAnnulus_radial_mass_general
#print axioms SpringerLean.thinAnnulus_radial_mass_small
