import SpringerLean.ActualSingleRampEnergy
import SpringerLean.Round1778AlignedComplexPhaseCost
import SpringerLean.Round1806TrueAxisSignedPower

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean.AnalyticRevision

set_option maxHeartbeats 1600000

/-- The energy's angular penalty pays the loss in the projected mth
power on the entire aligned angular window |k theta|<=2.8. -/
theorem aligned_phase_penalty_pays_projection
    {k m : ℕ} (hk : 751 ≤ k) (hm : m ≤ 2*k)
    {θ : ℝ} (hθ : |(k : ℝ)*θ| ≤ 14/5) :
    1-(3/14 : ℝ)*(Real.sin ((k : ℝ)*θ))^2 ≤ (Real.cos θ)^m := by
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
  have hcurv : (m : ℝ)/2 ≤ (3/14 : ℝ)*(k : ℝ)^2/100 := by
    have hquad := mul_nonneg (sub_nonneg.mpr hk') (Nat.cast_nonneg (α := ℝ) k)
    nlinarith [hquad]
  have hpay := mul_le_mul_of_nonneg_right hcurv (sq_nonneg θ)
  nlinarith [mul_le_mul_of_nonneg_left hcos (Nat.cast_nonneg m), hsq, hpay]

theorem aligned_complex_phase_cost_le_projection
    (beta v w : ℂ) (hv : ‖v‖=1) (k : ℕ) (hk : 751 ≤ k)
    (hphase : (beta*v^k)^2=1) {r θ : ℝ} (hr : 0 < r)
    (hw : w=v*(r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))
    (hθ : |(k : ℝ)*θ| ≤ 14/5) :
    ‖w‖^(2*k-2)-(3/14 : ℝ)*((beta*w^k).im^2/‖w‖^2) ≤
      ((conj v*w).re)^(2*k-2) := by
  have hnorm : ‖w‖=r := by
    rw [hw, norm_mul, norm_mul, hv, Complex.norm_exp_ofReal_mul_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    ring
  have hvv : conj v*v=1 := by simp [RCLike.conj_mul, hv]
  have hproj : (conj v*w).re=r*Real.cos θ := by
    have hh : conj v*w=(r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I) := by
      rw [hw]
      calc
        _ = (conj v*v)*(r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I) := by ring
        _ = _ := by rw [hvv, one_mul]
    rw [hh]
    simp [Complex.exp_mul_I, Complex.mul_re, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have him := phaseRay_power_im_sq beta v k hphase r θ
  rw [← hw] at him
  have hrpow : r^(2*k)=r^(2*k-2)*r^2 := by
    rw [← pow_add]
    congr 1
    omega
  have hpot : (beta*w^k).im^2/‖w‖^2=r^(2*k-2)*(Real.sin ((k : ℝ)*θ))^2 := by
    rw [him, hnorm, hrpow]
    field_simp [hr.ne']
  rw [hpot, hnorm, hproj, mul_pow]
  have hs := aligned_phase_penalty_pays_projection hk (by omega : 2*k-2 ≤ 2*k) hθ
  have hh := mul_le_mul_of_nonneg_left hs (pow_nonneg hr.le (2*k-2))
  nlinarith

/-- Actual-F pointwise domination once the geometric aligned cone
and positive projection have been established. -/
theorem actualSignedPhaseDensity_le_projected_of_aligned_polar
    (F : ℂ → ℂ) (beta v z : ℂ) (hv : ‖v‖=1) (k : ℕ) (hk : 751 ≤ k)
    (hphase : (beta*v^k)^2=1) {r θ : ℝ} (hr : 0 < r)
    (hw : actualHarmonic F z=v*(r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))
    (hθ : |(k : ℝ)*θ| ≤ 14/5)
    (hx : 0 ≤ (conj v*actualHarmonic F z).re) :
    singleRampSignedDensity F k beta z ≤
      (max ((conj v*actualHarmonic F z).re) 0)^(2*k-2)/(2 : ℝ)^(2*k-2) := by
  unfold singleRampSignedDensity actualHarmonicPhasePotentialDensity actualHarmonicPhaseField
  rw [max_eq_left hx]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact aligned_complex_phase_cost_le_projection beta v (actualHarmonic F z) hv k hk hphase hr hw hθ

/-- The coarse true-axis logarithmic budget implies the required
lower-power domination, with no optimized sine constants. -/
theorem trueAxis_signed_power_lt_lower
    (N : ℕ) (hN : 750 ≤ N) {u s h gamma theta Lambda : ℝ}
    (hu : 0 < u) (hs : 0 ≤ s) (hsu : s=2*(N : ℝ)*(1-u))
    (hLambda : 0 < Lambda) (hlogLambda : -14 < (2*(N : ℝ))*Real.log Lambda)
    (hcost : (2*(N : ℝ))^2*h^2/2 ≤ 1/6+(5/8 : ℝ)*s)
    (hgammaLo : Real.pi/3 ≤ |gamma|) (hgammaHi : |gamma| ≤ Real.pi/2)
    (hclose : s ≤ 1 → |theta| ≤ 2/3) (hshort : s ≤ 2 → |theta| ≤ 6/7) :
    u^(2*N)*(1+h^2)^N*(1-(3/14 : ℝ)*(Real.sin (gamma-theta))^2) <
      Lambda*u^(2*N-8) := by
  let m := 2*(N : ℝ)
  let f := 1-(3/14 : ℝ)*(Real.sin (gamma-theta))^2
  have hm : (1500 : ℝ) ≤ m := by dsimp [m]; exact_mod_cast (by omega : 1500 ≤ 2*N)
  have hm0 : 0 < m := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hf : 0 < f := by
    have hh := Real.sin_sq_add_cos_sq (gamma-theta)
    have hc := sq_nonneg (Real.cos (gamma-theta))
    dsimp [f]
    nlinarith
  have hH : 0 < 1+h^2 := by positivity
  have hU : 0 < u^(2*N) := pow_pos hu _
  have hP : 0 < (1+h^2)^N := pow_pos hH _
  have hUl : 0 < u^(2*N-8) := pow_pos hu _
  have hlogu := Real.log_le_sub_one_of_pos hu
  have hlogh := Real.log_le_sub_one_of_pos hH
  have hlogf := Real.log_le_sub_one_of_pos hf
  have hmu := mul_le_mul_of_nonneg_left hlogu hm0.le
  have hmh := mul_le_mul_of_nonneg_left hlogh (mul_nonneg hm0.le hN0)
  have hmf := mul_le_mul_of_nonneg_left hlogf hm0.le
  have hnegative' := SingleRamp.trueAxisSign m s gamma theta hm hs hgammaLo hgammaHi hclose hshort
  have hnegative : 14+m^2*h^2/2-8*s-(3/14 : ℝ)*m*(Real.sin (gamma-theta))^2 < 0 := by
    linarith [hnegative', hcost]
  change u^(2*N)*(1+h^2)^N*f < Lambda*u^(2*N-8)
  apply (Real.log_lt_log_iff (mul_pos (mul_pos hU hP) hf) (mul_pos hLambda hUl)).mp
  rw [Real.log_mul (mul_pos hU hP).ne' hf.ne', Real.log_mul hU.ne' hP.ne',
    Real.log_mul hLambda.ne' hUl.ne', Real.log_pow, Real.log_pow, Real.log_pow]
  rw [Nat.cast_sub (by omega : 8 ≤ 2*N)]
  push_cast
  apply (mul_lt_mul_iff_left₀ hm0).mp
  dsimp [m, f] at *
  nlinarith [hmu,hmh,hmf,hnegative,hlogLambda,hsu]

end SpringerLean.AnalyticRevision
