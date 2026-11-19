import SpringerLean.Round1434MovingArcThirdMoment
import SpringerLean.Round1374HalfCosMoments
import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory

namespace SpringerLean
set_option maxHeartbeats 200000

/-- Consecutive half-circle cosine moments have an exact product.
This gives the sharp Gaussian-scale constant without a Gaussian
integral. -/
theorem halfCosMoment_consecutive_product (k : ℕ) :
    halfCosMoment (k+1)*halfCosMoment k =
      Real.pi/(2*((k+1:ℕ):ℝ)) := by
  induction k using Nat.twoStepInduction with
  | zero =>
      have hC0 : halfCosMoment 0=Real.pi/2 := by
        unfold halfCosMoment
        simp
      have hC1 : halfCosMoment 1=1 := by
        unfold halfCosMoment
        simp [integral_cos]
      simp [hC0,hC1]
  | one =>
      have hC1 : halfCosMoment 1=1 := by
        unfold halfCosMoment
        simp [integral_cos]
      have hC0 : halfCosMoment 0=Real.pi/2 := by
        unfold halfCosMoment
        simp
      have hC2 : halfCosMoment 2=Real.pi/4 := by
        have h := halfCosMoment_succ_succ 0
        norm_num [hC0] at h
        linarith
      norm_num [hC1,hC2]
  | more k ih _ =>
      have hrec₁ := halfCosMoment_succ_succ (k+1)
      have hrec₂ := halfCosMoment_succ_succ k
      have hindex₁ : k+1+2=k+3 := by omega
      have hindex₂ : k+2=k+2 := rfl
      rw [hindex₁] at hrec₁
      change halfCosMoment (k+3)=
        (((k+2:ℕ):ℝ)/((k+3:ℕ):ℝ))*halfCosMoment (k+1) at hrec₁
      change halfCosMoment (k+2)=
        (((k+1:ℕ):ℝ)/((k+2:ℕ):ℝ))*halfCosMoment k at hrec₂
      change halfCosMoment (k+3)*halfCosMoment (k+2)=
        Real.pi/(2*((k+3:ℕ):ℝ))
      rw [hrec₁,hrec₂]
      calc
        (((k+2:ℕ):ℝ)/((k+3:ℕ):ℝ))*halfCosMoment (k+1)*
            ((((k+1:ℕ):ℝ)/((k+2:ℕ):ℝ))*halfCosMoment k) =
          (((k+2:ℕ):ℝ)/((k+3:ℕ):ℝ))*
            (((k+1:ℕ):ℝ)/((k+2:ℕ):ℝ))*
              (halfCosMoment (k+1)*halfCosMoment k) := by ring
        _ = (((k+2:ℕ):ℝ)/((k+3:ℕ):ℝ))*
            (((k+1:ℕ):ℝ)/((k+2:ℕ):ℝ))*
              (Real.pi/(2*((k+1:ℕ):ℝ))) := by rw [ih]
        _ = Real.pi/(2*((k+3:ℕ):ℝ)) := by
          field_simp

/-- Monotonicity of the cosine moment in its exponent. -/
theorem halfCosMoment_succ_le (k : ℕ) :
    halfCosMoment (k+1) ≤ halfCosMoment k := by
  unfold halfCosMoment
  apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    ((by fun_prop : Continuous (fun θ : ℝ => Real.cos θ^(k+1))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun θ : ℝ => Real.cos θ^k)).intervalIntegrable _ _)
  intro θ hθ
  have hcos0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hpow0 : 0 ≤ Real.cos θ^k := pow_nonneg hcos0 k
  rw [pow_succ]
  nlinarith [mul_nonneg hpow0 (sub_nonneg.mpr hcos1)]

/-- For every positive exponent, the normalized cosine moment has
square at most `2/(π n)`. -/
theorem normalizedHalfCosMoment_sq_le (n : ℕ) (hn : 1 ≤ n) :
    ((2/Real.pi)*halfCosMoment n)^2 ≤
      2/(Real.pi*(n:ℝ)) := by
  have hk : n-1+1=n := by omega
  have hprod := halfCosMoment_consecutive_product (n-1)
  rw [hk] at hprod
  have hmono := halfCosMoment_succ_le (n-1)
  rw [hk] at hmono
  have hC0 : 0 ≤ halfCosMoment n :=
    (EulerSine.integral_cos_pow_pos n).le
  have hmult := mul_le_mul_of_nonneg_left hmono hC0
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hpi := Real.pi_pos
  have hbound : halfCosMoment n^2 ≤
      Real.pi/(2*(n:ℝ)) := by
    nlinarith [hprod,hmult]
  have hmul := mul_le_mul_of_nonneg_left hbound
    (sq_nonneg (2/Real.pi))
  calc
    (2/Real.pi*halfCosMoment n)^2 =
        (2/Real.pi)^2*halfCosMoment n^2 := by ring
    _ ≤ (2/Real.pi)^2*(Real.pi/(2*(n:ℝ))) := hmul
    _ = 2/(Real.pi*(n:ℝ)) := by
      field_simp [ne_of_gt hpi,ne_of_gt hn0]

/-- The comparison-circle moment has a strict `0.8` Gaussian-scale
upper bound. It follows from the exact consecutive-moment product
and `π>25/8`. -/
theorem comparisonCircleMoment_four_fifths_upper
    (n : ℕ) (hn : 1 ≤ n) :
    Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1 <
      (4/5:ℝ)*(2:ℝ)^n/Real.sqrt (n:ℝ) := by
  let c : ℝ := (2/Real.pi)*halfCosMoment n
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hroot : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hn0
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpiLo : (25/8:ℝ) < Real.pi := by
    linarith [Real.pi_gt_d2]
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (by positivity)
      (EulerSine.integral_cos_pow_pos n).le
  have hsq : c^2 ≤ 2/(Real.pi*(n:ℝ)) :=
    normalizedHalfCosMoment_sq_le n hn
  have hnum : 2/(Real.pi*(n:ℝ)) < 16/(25*(n:ℝ)) := by
    apply (div_lt_div_iff₀ (by positivity : 0<Real.pi*(n:ℝ))
      (by positivity : 0<25*(n:ℝ))).2
    have hh := mul_lt_mul_of_pos_right hpiLo hn0
    nlinarith
  have htargetSq : ((4/5:ℝ)/Real.sqrt (n:ℝ))^2 =
      16/(25*(n:ℝ)) := by
    rw [div_pow,Real.sq_sqrt hn0.le]
    ring
  have hc : c < (4/5:ℝ)/Real.sqrt (n:ℝ) := by
    have htarget0 : 0 ≤ (4/5:ℝ)/Real.sqrt (n:ℝ) := by positivity
    nlinarith [hsq,hnum,htargetSq]
  have hI : Real.circleAverage
      (fun ζ : ℂ => |2*ζ.re|^n) 0 1 = (2:ℝ)^n*c := by
    rw [comparisonCircleMoment_eq_halfCosMoment]
    dsimp [c]
    rw [pow_succ]
    ring
  rw [hI]
  have hmul := mul_lt_mul_of_pos_left hc
    (show 0 < (2:ℝ)^n by positivity)
  calc
    (2:ℝ)^n*c < (2:ℝ)^n*((4/5:ℝ)/Real.sqrt (n:ℝ)) := hmul
    _ = (4/5:ℝ)*(2:ℝ)^n/Real.sqrt (n:ℝ) := by ring

end SpringerLean

#print axioms SpringerLean.halfCosMoment_consecutive_product
#print axioms SpringerLean.normalizedHalfCosMoment_sq_le
#print axioms SpringerLean.comparisonCircleMoment_four_fifths_upper
