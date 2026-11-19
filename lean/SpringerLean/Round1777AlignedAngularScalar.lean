import SpringerLean.Round1767TwoPowerPolynomial
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace SpringerLean
set_option maxHeartbeats 500000

/-- A deliberately coarse sine bound suffices at the large-order
threshold; no optimized numerical sine evaluation is required. -/
theorem sin_ge_tenth_on_short_phase {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 14/5) :
    x/10 ≤ Real.sin x := by
  let b : ℝ := 14/5
  let y : ℝ := Real.pi-b
  have hy0 : 0 ≤ y := by dsimp [y, b]; linarith [Real.pi_gt_d2]
  have hylo : (17/50 : ℝ) ≤ y := by dsimp [y, b]; linarith [Real.pi_gt_d2]
  have hyhi : y ≤ 7/20 := by dsimp [y, b]; linarith [Real.pi_lt_d2]
  have hy3 : y^3 ≤ (7/20 : ℝ)^3 := pow_le_pow_left₀ hy0 hyhi 3
  have hsin := Real.sin_ge_sub_cube hy0
  have hsinb : (3/10 : ℝ) ≤ Real.sin b := by
    rw [show b=Real.pi-y by dsimp [y]; ring, Real.sin_pi_sub]
    nlinarith
  have hbpi : b ≤ Real.pi := by dsimp [b]; linarith [Real.pi_gt_d2]
  have hb0 : (0 : ℝ) < b := by norm_num [b]
  have ht0 : 0 ≤ x/b := div_nonneg hx hb0.le
  have ht1 : x/b ≤ 1 := (div_le_one hb0).mpr hx1
  have hconc := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
    (show b ∈ Set.Icc 0 Real.pi from ⟨hb0.le, hbpi⟩)
    (sub_nonneg.mpr ht1) ht0 (by ring : (1-x/b)+x/b=1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sin_zero] at hconc
  have hxb : x/b*b=x := div_mul_cancel₀ x hb0.ne'
  rw [hxb] at hconc
  have hh := mul_le_mul_of_nonneg_left hsinb ht0
  dsimp [b] at hh hconc
  nlinarith

/-- The energy's angular penalty pays the loss in the projected mth
power on the entire aligned angular window |k theta|<=2.8. -/
theorem aligned_phase_penalty_pays_projection
    {k m : ℕ} (hk : 751 ≤ k) (hm : m ≤ 2*k)
    {θ : ℝ} (hθ : |(k : ℝ)*θ| ≤ 14/5) :
    1-(8/25 : ℝ)*(Real.sin ((k : ℝ)*θ))^2 ≤ (Real.cos θ)^m := by
  have hk' : (751 : ℝ) ≤ k := by exact_mod_cast hk
  have hm' : (m : ℝ) ≤ 2*k := by exact_mod_cast hm
  have hs := sin_ge_tenth_on_short_phase (abs_nonneg ((k : ℝ)*θ)) hθ
  have hsq : ((k : ℝ)*θ)^2/100 ≤ (Real.sin ((k : ℝ)*θ))^2 := by
    have hsn : 0 ≤ Real.sin |(k : ℝ)*θ| := by linarith [abs_nonneg ((k : ℝ)*θ)]
    have ha : 0 ≤ |(k : ℝ)*θ| := abs_nonneg _
    have hh := mul_nonneg (sub_nonneg.mpr hs) (add_nonneg hsn (div_nonneg ha (by norm_num : (0 : ℝ) ≤ 10)))
    have hsame : (Real.sin |(k : ℝ)*θ|)^2=(Real.sin ((k : ℝ)*θ))^2 := by
      by_cases ht : 0 ≤ (k : ℝ)*θ
      · rw [abs_of_nonneg ht]
      · rw [abs_of_neg (lt_of_not_ge ht), Real.sin_neg, neg_sq]
    nlinarith [sq_abs ((k : ℝ)*θ), hsame]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := θ)
  have hber := one_add_mul_sub_le_pow
    (show (-1 : ℝ) ≤ Real.cos θ from Real.neg_one_le_cos θ) m
  have hcurv : (m : ℝ)/2 ≤ (8/25 : ℝ)*(k : ℝ)^2/100 := by nlinarith
  have hpay := mul_le_mul_of_nonneg_right hcurv (sq_nonneg θ)
  nlinarith [mul_le_mul_of_nonneg_left hcos (Nat.cast_nonneg m), hsq, hpay]

end SpringerLean

#print axioms SpringerLean.aligned_phase_penalty_pays_projection
