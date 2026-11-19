import SpringerLean.Round1388ExpThreeHalves
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace SpringerLean

theorem coarseArc_power_factor_lower (n : ℕ) (hn : 1501 ≤ n) :
    (2/9 : ℝ) < (1-3/(2*(n:ℝ)))^(n-2) := by
  let u : ℝ := 3/(2*(n:ℝ))
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hnlarge : (1501:ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < 2*(n:ℝ) := by positivity
  have hu0 : 0 < u := by dsimp [u]; positivity
  have huHalf : u < 1/2 := by
    dsimp [u]
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hOne : 0 < 1-u := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hOne
  have hm : (0:ℝ) ≤ ((n-2:ℕ):ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog hm
  have hNat : ((n-2:ℕ):ℝ) = (n:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2≤n)]
    norm_num
  have haux : -3/2 ≤ ((n-2:ℕ):ℝ)*(1-(1-u)⁻¹) := by
    rw [hNat]
    have hOneNe : 1-u ≠ 0 := ne_of_gt hOne
    have hfrac : 1-(1-u)⁻¹ = -u/(1-u) := by
      field_simp [hOneNe]
      ring
    rw [hfrac]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hOne).2
    dsimp [u]
    field_simp [hn0.ne']
    nlinarith
  have hlogBound : -3/2 ≤ ((n-2:ℕ):ℝ)*Real.log (1-u) :=
    haux.trans hmul
  have hExp := Real.exp_le_exp.mpr hlogBound
  have hpow : Real.exp (((n-2:ℕ):ℝ)*Real.log (1-u)) =
      (1-u)^(n-2) := by
    rw [Real.exp_nat_mul, Real.exp_log hOne]
  have hrec : (2/9 : ℝ) < Real.exp (-3/2 : ℝ) := by
    rw [show (-3/2 : ℝ)=-(3/2 : ℝ) by ring, Real.exp_neg]
    have hrec' : (2/9 : ℝ) < 1/Real.exp (3/2 : ℝ) := by
      apply (lt_div_iff₀ (Real.exp_pos _)).2
      have hh := exp_three_halves_lt_nine_halves
      nlinarith
    simpa only [one_div] using hrec'
  change (2/9 : ℝ) < (1-u)^(n-2)
  exact hrec.trans_le (hExp.trans_eq hpow)

end SpringerLean

#print axioms SpringerLean.coarseArc_power_factor_lower
