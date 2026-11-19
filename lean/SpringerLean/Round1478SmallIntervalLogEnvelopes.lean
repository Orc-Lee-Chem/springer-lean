import SpringerLean.Round1477SmallIntervalBaseLog

namespace SpringerLean
set_option maxHeartbeats 220000

/-- The cubic logarithm at a smaller deficit is controlled by its
value at `3/20`; the square-root factor pays the added logarithm. -/
theorem refinedAffine_small_log_t_envelope
    (n : ℕ) (hn : 1501 ≤ n) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 3/20) :
    Real.sqrt t*(Real.log (2*(n:ℝ)/t))^3 ≤
      Real.sqrt (3/20:ℝ)*
        (Real.log (2*(n:ℝ)/(3/20:ℝ)))^3 := by
  let N : ℝ := n
  let c : ℝ := Real.log (2*N/(3/20:ℝ))
  let u : ℝ := Real.log ((3/20:ℝ)/t)
  have hN : (1501:ℝ) ≤ N := by dsimp [N]; exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hc : 6 ≤ c := by
    have harg : (3002:ℝ) ≤ 2*N/(3/20:ℝ) := by
      dsimp [N]
      nlinarith
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<3002) harg
    dsimp [c]
    linarith [log_3002_gt_six]
  have hratio : (1:ℝ) ≤ (3/20:ℝ)/t := by
    apply (le_div_iff₀ ht0).2
    linarith
  have hu : 0 ≤ u := Real.log_nonneg hratio
  have hL : Real.log (2*N/t)=c+u := by
    have heq : 2*N/t=(2*N/(3/20:ℝ))*((3/20:ℝ)/t) := by
      field_simp
    rw [heq,Real.log_mul
      (by positivity : (2*N/(3/20:ℝ)) ≠ 0)
      (by positivity : ((3/20:ℝ)/t) ≠ 0)]
  have hEnv := logCube_exponential_envelope hc hu
  have hsquare : (Real.sqrt t*Real.exp (u/2))^2=3/20 := by
    rw [mul_pow,Real.sq_sqrt ht0.le,←Real.exp_nat_mul]
    have harg : Real.exp u=(3/20:ℝ)/t := Real.exp_log (by positivity)
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(u/2)=u by ring,harg]
    field_simp
  have hsqrtprod : Real.sqrt t*Real.exp (u/2)=Real.sqrt (3/20:ℝ) := by
    have hsqrt := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3/20)
    have hprod : 0 ≤ Real.sqrt t*Real.exp (u/2) := by positivity
    nlinarith [hprod,Real.sqrt_nonneg (3/20:ℝ)]
  have hmul := mul_le_mul_of_nonneg_left hEnv (Real.sqrt_nonneg t)
  change Real.sqrt t*(c+u)^3 ≤
    Real.sqrt t*(c^3*Real.exp (u/2)) at hmul
  calc
    Real.sqrt t*(Real.log (2*(n:ℝ)/t))^3 =
        Real.sqrt t*(c+u)^3 := by rw [show (n:ℝ)=N by rfl,hL]
    _ ≤ Real.sqrt t*(c^3*Real.exp (u/2)) := hmul
    _ = Real.sqrt (3/20:ℝ)*c^3 := by
      rw [show Real.sqrt t*(c^3*Real.exp (u/2)) =
        c^3*(Real.sqrt t*Real.exp (u/2)) by ring,hsqrtprod]
      ring
    _ = _ := rfl

/-- At fixed base deficit, the cubic logarithm divided by order
decreases from `n=1501`. -/
theorem refinedAffine_small_log_n_envelope
    (n : ℕ) (hn : 1501 ≤ n) :
    (Real.log (2*(n:ℝ)/(3/20:ℝ)))^3 ≤
      ((n:ℝ)/1501)*
        (Real.log (2*(1501:ℝ)/(3/20:ℝ)))^3 := by
  let N : ℝ := n
  let c : ℝ := Real.log (2*(1501:ℝ)/(3/20:ℝ))
  let u : ℝ := Real.log (N/1501)
  have hN : (1501:ℝ) ≤ N := by dsimp [N]; exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hratio : (1:ℝ) ≤ N/1501 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<1501)).2
    linarith
  have hratio0 : 0 < N/1501 := by positivity
  have hu : 0 ≤ u := Real.log_nonneg hratio
  have hc : 6 ≤ c := by
    have harg : (3002:ℝ) ≤ 2*(1501:ℝ)/(3/20:ℝ) := by norm_num
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<3002) harg
    dsimp [c]
    linarith [log_3002_gt_six]
  have harg : 2*N/(3/20:ℝ) =
      (2*(1501:ℝ)/(3/20:ℝ))*(N/1501) := by ring
  have hL : Real.log (2*N/(3/20:ℝ))=c+u := by
    rw [harg,Real.log_mul
      (by norm_num : (2*(1501:ℝ)/(3/20:ℝ)) ≠ 0)
      (ne_of_gt hratio0)]
  have hEnv := logCube_exponential_envelope hc hu
  have hExp : Real.exp (u/2) ≤ Real.exp u :=
    Real.exp_le_exp.mpr (by linarith)
  have hscaled := mul_le_mul_of_nonneg_left hExp
    (pow_nonneg (by linarith : 0 ≤ c) 3)
  have hle : (c+u)^3 ≤ c^3*(N/1501) := by
    calc
      (c+u)^3 ≤ c^3*Real.exp (u/2) := hEnv
      _ ≤ c^3*Real.exp u := hscaled
      _ = c^3*(N/1501) := by rw [show u=Real.log (N/1501) by rfl,Real.exp_log hratio0]
  rw [show (n:ℝ)=N by rfl,hL]
  dsimp [c]
  dsimp [c] at hle
  nlinarith [hle]

end SpringerLean

#print axioms SpringerLean.refinedAffine_small_log_t_envelope
#print axioms SpringerLean.refinedAffine_small_log_n_envelope
