import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/- Independent check of the scalar multiplier comparison. The two branches
   use x = min (12*t) (9/5); q is the nonnegative quadratic test variable. -/
namespace SingleRamp

private theorem quadratic (a b d q : ℝ) (ha : 0 < a)
    (h : b ^ 2 ≤ 4 * a * (9 / 4 - d)) :
    d + b*q - a*q^2 ≤ 9/4 := by
  by_contra! hbad
  nlinarith [sq_nonneg (2*a*q-b), mul_pos ha (sub_pos.mpr hbad)]

private theorem transfer (a b d aa bb dd q : ℝ)
    (ha : 0 < a) (hd : 0 ≤ d) (hq : 0 ≤ q)
    (hm : b^2 ≤ 4*a*(9/4-d)) (hA : 99/100*a ≤ aa)
    (hB : bb ≤ 101/100*b) (hD : dd ≤ 101/100*d) :
    dd + bb*q - aa*q^2 ≤ 7/3 := by
  have h0 := quadratic a b d (99/101*q) ha hm
  nlinarith [mul_le_mul_of_nonneg_right hA (sq_nonneg q),
    mul_le_mul_of_nonneg_right hB hq]

theorem singleRampScalar (K q : ℝ) (hK : 751 ≤ K) (hq : 0 ≤ q) :
    (∀ x : ℝ, 0 ≤ x → x ≤ 9/5 →
      (1+2/(K-1))*x/4 +
        (3*(1+1/(K-1))+(2/3+1/(2*(K-1))+1/(3*K))*x)*q -
        (1+(1-1/K)*x)*q^2 ≤ 7/3) ∧
    9/20*(1+1/(K-1)) + (12/5+3/(10*K))*q -
      (4/5-6/(5*K))*q^2 ≤ 7/3 := by
  have hk : 0 < K := by linarith
  have hp : 0 < K-1 := by linarith
  let u := (1:ℝ)/K
  let e := (1:ℝ)/(K-1)
  have hu : u ≤ 1/700 := by dsimp [u]; apply (div_le_iff₀ hk).2; linarith
  have he : e ≤ 1/700 := by dsimp [e]; apply (div_le_iff₀ hp).2; linarith
  constructor
  · intro x hx hx'
    have ex := mul_le_mul_of_nonneg_right he hx
    have ux := mul_le_mul_of_nonneg_right hu hx
    have h1 : 1/(2*(K-1)) = e/2 := by dsimp [e]; field_simp
    have h2 : 1/(3*K) = u/3 := by dsimp [u]; field_simp
    have h3 : 2/(K-1) = 2*e := by dsimp [e]; field_simp
    rw [h1,h2,h3]
    change (1+2*e)*x/4 + (3*(1+e)+(2/3+e/2+u/3)*x)*q -
      (1+(1-u)*x)*q^2 ≤ 7/3
    apply transfer (1+x) (3+2*x/3) (x/4) _ _ _ q (by linarith) (by linarith) hq
    · nlinarith [mul_nonneg hx (show 0 ≤ 4-13*x/9 by linarith)]
    · nlinarith
    · nlinarith
    · nlinarith
  · have h1 : 3/(10*K) = 3*u/10 := by dsimp [u]; field_simp
    have h2 : 6/(5*K) = 6*u/5 := by dsimp [u]; field_simp
    rw [h1,h2]
    change 9/20*(1+e) + (12/5+3*u/10)*q - (4/5-6*u/5)*q^2 ≤ 7/3
    apply transfer (4/5) (12/5) (9/20) _ _ _ q (by norm_num) (by norm_num) hq
    · norm_num
    · linarith
    · linarith
    · linarith

theorem alignedBudget (K : ℝ) (hK : 751 ≤ K) :
    K - 1 ≤ 3 / 1400 * K ^ 2 := by
  nlinarith [mul_nonneg (show 0 ≤ K-751 by linarith)
    (show 0 ≤ K by linarith)]

theorem axisBudgets (m s : ℝ) (hm : 1500 ≤ m) (hs : 0 ≤ s) :
    (s ≤ 1 → 14+1/6+5/8*s-8*s < 3/14*m*(1/16)) ∧
    (1 ≤ s → 14+1/6+5/8*s-8*s < 3/14*m*(1/30)) := by
  constructor <;> intro _ <;> linarith

/-- The quadratic extracted from the drift flux with f = chi/6. -/
noncomputable def fluxCost (K t chi slope q : ℝ) : ℝ :=
  let f := chi/6
  let fp := slope/6
  let h := f+t*fp
  let a := chi+fp-(2*f+2*|h|)/K-1
  let b := chi+|2*f-K*slope/(4*(K-1))|+
    t*|slope|/(2*(K-1))+|h|/K
  let d := (K*chi+t*|slope|)/(4*(K-1))
  d+b*q-a*q^2

theorem linearPiece (K t q : ℝ) (hK : 751 ≤ K) (ht : 0 ≤ t)
    (hc : t ≤ 3/20) (hq : 0 ≤ q) :
    fluxCost K t (12*t) 12 q ≤ 7/3 := by
  have hk : K ≠ 0 := by linarith
  have hp : 0 < K-1 := by linarith
  have hr : K*12/(4*(K-1)) ≥ (3:ℝ) := by
    apply (le_div_iff₀ (by linarith : 0 < 4*(K-1))).2
    linarith
  have hneg : 2*(12*t/6)-K*12/(4*(K-1)) ≤ 0 := by linarith
  have hh : 0 ≤ 12*t/6+t*(12/6) := by linarith
  apply le_trans (le_of_eq ?_) ((singleRampScalar K q hK hq).1 (12*t)
    (by linarith) (by linarith))
  unfold fluxCost
  dsimp only
  rw [abs_of_nonneg hh, abs_of_nonpos hneg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 12)]
  field_simp [hk, ne_of_gt hp]
  ring

theorem constantPiece (K t q : ℝ) (hK : 751 ≤ K) (hq : 0 ≤ q) :
    fluxCost K t (9/5) 0 q ≤ 7/3 := by
  have hk : K ≠ 0 := by linarith
  have hp : 0 < K-1 := by linarith
  apply le_trans (le_of_eq ?_) (singleRampScalar K q hK hq).2
  unfold fluxCost
  dsimp only
  norm_num [abs_of_nonneg]
  field_simp [hk, ne_of_gt hp]
  ring

theorem clippedLinearFlux (K t q : ℝ) (hK : 751 ≤ K) (ht : 0 ≤ t)
    (hq : 0 ≤ q) :
    fluxCost K t (min (12*t) (9/5)) (if t ≤ 3/20 then 12 else 0) q ≤ 7/3 := by
  split_ifs with hc
  · rw [min_eq_left (by linarith)]
    exact linearPiece K t q hK ht hc hq
  · rw [min_eq_right (by linarith)]
    exact constantPiece K t q hK hq

theorem smallAngleFromStrip (K s v : ℝ) (hK : 751 ≤ K)
    (hs : 0 ≤ s) (hc : s ≤ 1)
    (hstrip : v^2 ≤ (K/(2*K-2))^2 * (1/3+5*s/4)) : |v| ≤ 2/3 := by
  have hp : 0 < 2*K-2 := by linarith
  have hr : K/(2*K-2) ≤ 751/1500 := by
    apply (div_le_iff₀ hp).2
    linarith
  have h0 : 0 ≤ K/(2*K-2) := div_nonneg (by linarith) hp.le
  have hsq := pow_le_pow_left₀ h0 hr 2
  have hprod := mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ 1/3+5*s/4)
  nlinarith [sq_abs v, sq_nonneg (|v| - 2/3)]

private theorem sinFloor (g v c a : ℝ)
    (hgl : Real.pi/3 ≤ |g|) (hgu : |g| ≤ Real.pi/2) (hv : |v| ≤ c)
    (ha : 0 ≤ a) (hl : a ≤ Real.pi/3-c)
    (hu : Real.pi/2+c ≤ Real.pi-a) :
    a-a^3/6 ≤ |Real.sin (g-v)| := by
  have h1 : |g| ≤ |g-v|+|v| := by
    simpa using abs_add_le (g-v) v
  have h2 : |g-v| ≤ |g|+|v| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le g (-v)
  have hlo : a ≤ |g-v| := by linarith
  have hhi : |g-v| ≤ Real.pi-a := by linarith only [h2, hgu, hv, hu]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith : |g-v| ≤ Real.pi)]
  apply le_trans (Real.sin_ge_sub_cube ha)
  by_cases hx : |g-v| ≤ Real.pi/2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hx hlo
  · rw [← Real.sin_pi_sub |g-v|]
    apply Real.sin_le_sin_of_le_of_le_pi_div_two <;> linarith [Real.pi_pos]

/-- The true-axis branch after the geometric angle estimates.
    Here v is the scaled angle k*h, and m is the even exponent. -/
theorem trueAxisSign (m s g v : ℝ) (hm : 1500 ≤ m) (hs : 0 ≤ s)
    (hgl : Real.pi/3 ≤ |g|) (hgu : |g| ≤ Real.pi/2)
    (close : s ≤ 1 → |v| ≤ 2/3) (middle : s ≤ 2 → |v| ≤ 6/7) :
    14+1/6+5/8*s-8*s-3/14*m*(Real.sin (g-v))^2 < 0 := by
  by_cases hc : s ≤ 1
  · have hf := sinFloor g v (2/3) (1/3) hgl hgu (close hc) (by norm_num)
      (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three])
    have hab : (1/4:ℝ) ≤ |Real.sin (g-v)| := by norm_num at hf; linarith
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/4) hab 2
    rw [sq_abs] at hsq
    nlinarith [(axisBudgets m s hm hs).1 hc,
      mul_le_mul_of_nonneg_left hsq (by linarith : 0 ≤ m)]
  · by_cases hc2 : s ≤ 2
    · have hf := sinFloor g v (6/7) (199/1050) hgl hgu (middle hc2) (by norm_num)
        (by linarith [Real.pi_gt_d2]) (by linarith [Real.pi_gt_d2])
      have hab : (3/16:ℝ) ≤ |Real.sin (g-v)| := by norm_num at hf; linarith
      have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/16) hab 2
      rw [sq_abs] at hsq
      nlinarith [(axisBudgets m s hm hs).2 (by linarith),
        mul_le_mul_of_nonneg_left hsq (by linarith : 0 ≤ m)]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ m) (sq_nonneg (Real.sin (g-v)))]

#print axioms smallAngleFromStrip
#print axioms trueAxisSign
#print axioms clippedLinearFlux
#print axioms singleRampScalar
#print axioms alignedBudget
#print axioms axisBudgets
end SingleRamp
