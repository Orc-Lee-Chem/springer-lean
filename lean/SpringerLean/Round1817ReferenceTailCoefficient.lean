import SpringerLean.Round1815TruncatedTwelveBudget

namespace SpringerLean
set_option maxHeartbeats 800000

/-- All constants in the exponential-tail estimate are controlled by
one common rational bound, uniformly in m and the crossover parameter. -/
theorem reference_tail_coefficient_lt_twelve
    (m : ℕ) (hm : 1500 ≤ m) (a : ℝ) (ha : 6 ≤ a) (hau : a ≤ (m : ℝ)/5) :
    let c := 1-a/(m : ℝ)
    let σ := ((m : ℝ)-8)/((m : ℝ)-a)
    (16*Real.sqrt 2/Real.pi)*(c^(m-1)*Real.exp a)*
      (1/σ^2+1/(a*σ^3)) < 12 := by
  have hm' : (1500 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have ha0 : 0 < a := by linarith
  have hadiv : a/(m : ℝ) ≤ 1/5 := (div_le_iff₀ hm0).mpr (by linarith)
  have hc0 : 0 ≤ 1-a/(m : ℝ) := by linarith
  have hden : 0 < (m : ℝ)-a := by linarith
  have hσ : (99/100 : ℝ) < ((m : ℝ)-8)/((m : ℝ)-a) := by
    apply (lt_div_iff₀ hden).mpr
    linarith
  let σ := ((m : ℝ)-8)/((m : ℝ)-a)
  have hσ0 : 0 < σ := by dsimp [σ]; linarith
  have hinv : 1/σ ≤ (100/99 : ℝ) := by
    apply (div_le_iff₀ hσ0).mpr
    change 99/100 < σ at hσ
    linarith
  have hpow := pow_le_pow_left₀ hc0
    (show 1-a/(m : ℝ) ≤ Real.exp (-a/(m : ℝ)) by
      have hh := Real.add_one_le_exp (-a/(m : ℝ))
      convert hh using 1 <;> ring) (m-1)
  rw [←Real.exp_nat_mul] at hpow
  have hcast : ((m-1 : ℕ) : ℝ)=(m : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m),Nat.cast_one]
  have hexpid : ((m-1 : ℕ) : ℝ)*(-a/(m : ℝ))+a=a/(m : ℝ) := by
    rw [hcast]
    field_simp
    <;> ring
  have he := mul_le_mul_of_nonneg_right hpow (Real.exp_pos a).le
  rw [←Real.exp_add,hexpid] at he
  have hsmall := Real.exp_bound_div_one_sub_of_interval'
    (by norm_num : (0 : ℝ) < 1/5) (by norm_num : (1/5 : ℝ) < 1)
  norm_num only at hsmall
  have heupper : (1-a/(m : ℝ))^(m-1)*Real.exp a < 5/4 :=
    he.trans_lt ((Real.exp_le_exp.mpr hadiv).trans_lt hsmall)
  have hfac : 16*Real.sqrt 2/Real.pi < 8 := by
    have hs : Real.sqrt 2 < 3/2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    apply (div_lt_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three]
  have hsum : 1/σ^2+1/(a*σ^3) ≤ (100/99 : ℝ)^2+(1/6 : ℝ)*(100/99 : ℝ)^3 := by
    have hi2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1/σ) hinv 2
    have hi3 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1/σ) hinv 3
    have hiA : 1/a ≤ (1/6 : ℝ) := by apply (div_le_iff₀ ha0).mpr; linarith
    have hiA3 := mul_le_mul hiA hi3 (by positivity : (0 : ℝ) ≤ (1/σ)^3) (by norm_num : (0 : ℝ) ≤ 1/6)
    have heq2 : 1/σ^2=(1/σ)^2 := by simp only [div_pow,one_pow]
    have heq3 : 1/(a*σ^3)=(1/a)*(1/σ)^3 := by field_simp
    rw [heq2,heq3]
    linarith
  have hleft : 0 ≤ 16*Real.sqrt 2/Real.pi := by positivity
  have hmid : 0 ≤ (1-a/(m : ℝ))^(m-1)*Real.exp a := by positivity
  have hsum0 : 0 ≤ 1/σ^2+1/(a*σ^3) := by positivity
  dsimp only
  change (16*Real.sqrt 2/Real.pi)*((1-a/(m : ℝ))^(m-1)*Real.exp a)*
    (1/σ^2+1/(a*σ^3)) < 12
  calc
    _ ≤ 8*(5/4)*((100/99 : ℝ)^2+(1/6 : ℝ)*(100/99 : ℝ)^3) := by
      gcongr
    _ < 12 := by norm_num

end SpringerLean

#print axioms SpringerLean.reference_tail_coefficient_lt_twelve
