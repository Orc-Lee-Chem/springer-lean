import SpringerLean.Round1802PowerExpAntitone
import SpringerLean.Round1782TruncatedModelBudget

namespace SpringerLean
set_option maxHeartbeats 900000

theorem exp_three_gt_twenty : (20 : ℝ) < Real.exp 3 := by
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 9
  norm_num [Finset.sum_range_succ] at hh
  linarith

/-- The independent a and L monotonicities replace implicit-root
monotonicity in the untruncated model budget. -/
theorem untruncated_twoPower_scalar_cost_lt_cubic
    {a L m D : ℝ} (ha : 6 ≤ a) (hL : 9 ≤ L) (hm : 0 < m) (hD : 0 < D)
    (hprod : a*D*L=9) (hmexp : 2*m=D*Real.exp L) :
    12*Real.exp (-a)*Real.sqrt a/m < D^3/40 := by
  have ha0 : 0 < a := by linarith
  have hL0 : 0 < L := by linarith
  have hs6 : (Real.sqrt 6)^2=6 := Real.sq_sqrt (by norm_num)
  have hs6pos : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hs6upper : Real.sqrt 6 < 5/2 := by nlinarith [Real.sqrt_nonneg 6]
  have hsa : (Real.sqrt a)^2=a := Real.sq_sqrt ha0.le
  have hroot : Real.sqrt a*Real.sqrt 6 ≤ a := by
    have hs : (Real.sqrt a*Real.sqrt 6)^2 ≤ a^2 := by
      rw [mul_pow, hsa, hs6]
      nlinarith
    nlinarith [Real.sqrt_nonneg a, mul_nonneg (Real.sqrt_nonneg a) hs6pos.le]
  have h5 := power_exp_neg_antitone 4 (by norm_num : (6 : ℝ) ∈ Set.Ici ((4 : ℝ)+1))
    (by change (4 : ℝ)+1 ≤ a; linarith : a ∈ Set.Ici ((4 : ℝ)+1)) ha
  have h4 := power_exp_neg_antitone 3 (by norm_num : (9 : ℝ) ∈ Set.Ici ((3 : ℝ)+1))
    (by change (3 : ℝ)+1 ≤ L; linarith : L ∈ Set.Ici ((3 : ℝ)+1)) hL
  change a^5*Real.exp (-a) ≤ (6 : ℝ)^5*Real.exp (-6) at h5
  change L^4*Real.exp (-L) ≤ (9 : ℝ)^4*Real.exp (-9) at h4
  have hrootmul := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ a^4*Real.exp (-a) by positivity)
  have hA : a^4*Real.sqrt a*Real.exp (-a) ≤ (6 : ℝ)^4*Real.sqrt 6*Real.exp (-6) := by
    have heq : (6 : ℝ)^4*Real.sqrt 6*Real.exp (-6)*Real.sqrt 6=(6 : ℝ)^5*Real.exp (-6) := by
      calc
        _ = (6 : ℝ)^4*Real.exp (-6)*(Real.sqrt 6)^2 := by ring
        _ = _ := by rw [hs6]; ring
    nlinarith [h5]
  have hAL := mul_le_mul hA h4 (by positivity : 0 ≤ L^4*Real.exp (-L))
    (by positivity : 0 ≤ (6 : ℝ)^4*Real.sqrt 6*Real.exp (-6))
  have hexpadd : Real.exp (-6)*Real.exp (-9)=Real.exp (-15) := by rw [←Real.exp_add]; norm_num
  have hratio : 12*Real.exp (-a)*Real.sqrt a/m/D^3=
      (24/(9 : ℝ)^4)*(a^4*Real.sqrt a*Real.exp (-a))*(L^4*Real.exp (-L)) := by
    have hmval : m=D*Real.exp L/2 := by linarith
    have hDval : D=9/(a*L) := by
      apply (eq_div_iff (mul_ne_zero ha0.ne' hL0.ne')).mpr
      nlinarith
    rw [hmval,hDval]
    simp only [Real.exp_neg]
    field_simp
    <;> ring
  have hratio_le : 12*Real.exp (-a)*Real.sqrt a/m/D^3 ≤
      24*(6 : ℝ)^4*Real.sqrt 6*Real.exp (-15) := by
    rw [hratio]
    have hh := mul_le_mul_of_nonneg_left hAL (by norm_num : (0 : ℝ) ≤ 24/(9 : ℝ)^4)
    rw [show (6 : ℝ)^4*Real.sqrt 6*Real.exp (-6)*((9 : ℝ)^4*Real.exp (-9))=
      (6 : ℝ)^4*Real.sqrt 6*(9 : ℝ)^4*(Real.exp (-6)*Real.exp (-9)) by ring,hexpadd] at hh
    nlinarith
  have he15 : (20 : ℝ)^5 < Real.exp 15 := by
    have hh := pow_lt_pow_left₀ exp_three_gt_twenty (by norm_num : (0 : ℝ) ≤ 20) (by norm_num : 5 ≠ 0)
    rw [show (15 : ℝ)=(5 : ℕ)*3 by norm_num,Real.exp_nat_mul]
    exact hh
  have hsmall : 24*(6 : ℝ)^4*Real.sqrt 6*Real.exp (-15) < 1/40 := by
    rw [Real.exp_neg, ←div_eq_mul_inv]
    apply (div_lt_iff₀ (Real.exp_pos _)).mpr
    nlinarith
  have hh := hratio_le.trans_lt hsmall
  exact (div_lt_iff₀ (by positivity : 0 < D^3)).mp hh |>.trans_eq (by ring)

end SpringerLean

#print axioms SpringerLean.untruncated_twoPower_scalar_cost_lt_cubic
