import SpringerLean.Round1817ReferenceTailCoefficient

namespace SpringerLean
set_option maxHeartbeats 600000

theorem eighth_power_tail_bound {c u : ℝ} (hu : 0 ≤ u) (huc : u ≤ c) :
    c^8-u^8 ≤ 8*(c-u)*c^7 := by
  have hc := hu.trans huc
  have hh := abs_pow_sub_pow_le (a := c) (b := u) (n := 8)
  have hp := pow_le_pow_left₀ hu huc 8
  simp only [abs_of_nonneg hc,abs_of_nonneg hu,max_eq_left huc,
    abs_of_nonneg (sub_nonneg.mpr huc),abs_of_nonneg (sub_nonneg.mpr hp),
    Nat.cast_ofNat,Nat.reduceSub] at hh
  nlinarith [hh]

theorem power_below_tangent_exponential {c u : ℝ}
    (hc : 0 < c) (hu : 0 ≤ u) (ell : ℕ) :
    u^ell ≤ c^ell*Real.exp (-((ell : ℝ)*(c-u)/c)) := by
  have hb := Real.add_one_le_exp (-(c-u)/c)
  have heq : -(c-u)/c+1=u/c := by field_simp; ring
  rw [heq] at hb
  have hbase := mul_le_mul_of_nonneg_left hb hc.le
  have huc : c*(u/c)=u := by field_simp
  rw [huc] at hbase
  have hh := pow_le_pow_left₀ hu hbase ell
  rw [mul_pow,←Real.exp_nat_mul] at hh
  have he : (ell : ℝ)*(-(c-u)/c) = -((ell : ℝ)*(c-u)/c) := by ring
  rwa [he] at hh

theorem sqrt_tail_tangent_bound {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    Real.sqrt s ≤ Real.sqrt a+(s-a)/(2*Real.sqrt a) := by
  have hsa := Real.sq_sqrt ha.le
  have hss := Real.sq_sqrt hs
  have hapos : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have heq : (Real.sqrt a+(s-a)/(2*Real.sqrt a))*(2*Real.sqrt a)=a+s := by
    field_simp
    nlinarith
  have hh : Real.sqrt s*(2*Real.sqrt a) ≤ a+s := by
    nlinarith [sq_nonneg (Real.sqrt s-Real.sqrt a)]
  have hdiv : Real.sqrt s ≤ (a+s)/(2*Real.sqrt a) :=
    (le_div_iff₀ (by positivity)).mpr hh
  have htarget : (a+s)/(2*Real.sqrt a)=Real.sqrt a+(s-a)/(2*Real.sqrt a) := by
    apply (div_eq_iff (by positivity : 2*Real.sqrt a ≠ 0)).mpr
    nlinarith [heq]
  simpa only [htarget] using hdiv

theorem power_excess_exponential_bound {c u : ℝ} (hc : 0 < c)
    (hu : 0 ≤ u) (huc : u ≤ c) (ell : ℕ) :
    u^ell*(c^8-u^8) ≤
      8*c^(ell+7)*(c-u)*Real.exp (-((ell : ℝ)*(c-u)/c)) := by
  have h₁ := eighth_power_tail_bound hu huc
  have h₂ := power_below_tangent_exponential hc hu ell
  have hp : 0 ≤ c^8-u^8 := sub_nonneg.mpr (pow_le_pow_left₀ hu huc _)
  have hh := mul_le_mul h₂ h₁ hp (by positivity : 0 ≤ c^ell*Real.exp (-((ell : ℝ)*(c-u)/c)))
  rw [pow_add]
  nlinarith [hh]

end SpringerLean

#print axioms SpringerLean.power_excess_exponential_bound
