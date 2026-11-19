import SpringerLean.Round1337PlatformScalar
import SpringerLean.Round1318Catalan359Scalar
import Mathlib.Analysis.Real.Pi.Bounds

namespace SpringerLean

/-- The Gaussian model cost has a uniform rational square-root bound.
The approximation `π < 3.15` leaves a strict margin. -/
theorem gaussian_model_factor_lt (n : ℕ) (hn : 1501 ≤ n) :
    Real.sqrt (Real.pi / ((n:ℝ)*(8/5)/Real.pi^2)) /
        (2*Real.pi) < (141/200 : ℝ)/Real.sqrt n := by
  let G : ℝ := Real.sqrt (Real.pi / ((n:ℝ)*(8/5)/Real.pi^2)) /
        (2*Real.pi)
  have hnR : (1501:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπb : Real.pi < (63/20:ℝ) := by
    have h := Real.pi_lt_d2
    norm_num at h ⊢
    exact h
  have hroot : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hn0
  have hG0 : 0 ≤ G := by dsimp [G]; positivity
  have hGsq : G^2 = (5*Real.pi)/(32*(n:ℝ)) := by
    dsimp [G]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have hTsq : ((141/200 : ℝ)/Real.sqrt n)^2 =
      (141^2 : ℝ)/(200^2*(n:ℝ)) := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
    ring
  have hsq : G^2 < ((141/200 : ℝ)/Real.sqrt n)^2 := by
    rw [hGsq, hTsq]
    apply (div_lt_div_iff₀ (by positivity : (0:ℝ) < 32*(n:ℝ))
      (by positivity : (0:ℝ) < 200^2*(n:ℝ))).2
    nlinarith [mul_lt_mul_of_pos_right hπb hn0]
  have hT0 : 0 ≤ (141/200 : ℝ)/Real.sqrt n := by positivity
  change G < (141/200 : ℝ)/Real.sqrt n
  nlinarith [sq_nonneg (G + (141/200 : ℝ)/Real.sqrt n)]

/-- At all orders `k ≥ 751`, the Gaussian one-end bound is strictly
below the normalized Catalan candidate. -/
theorem gaussian_platform_lt_normalizedCatalan
    (k : ℕ) (hk : 751 ≤ k) :
    (39/40 : ℝ)^(2*k-1) +
      Real.sqrt (Real.pi / (((2*k-1:ℕ):ℝ)*(8/5)/Real.pi^2)) /
        (2*Real.pi) < normalizedCatalanOddMoment (k-1) := by
  let n : ℕ := 2*k-1
  have hn : 1501 ≤ n := by dsimp [n]; omega
  have hnR : (1501:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hkR : (751:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hnform : (n:ℝ) = 2*(k:ℝ)-1 := by
    dsimp [n]
    rw [Nat.cast_sub (by omega : 1 ≤ 2*k)]
    push_cast
    ring
  have hrootn : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hn0
  have hrootk : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.2 hk0
  have hrootn_le_n : Real.sqrt (n:ℝ) ≤ n := by
    nlinarith [Real.sq_sqrt hn0.le]
  have hplatform0 := platform_exp_small n hn
  have hplatform : (39/40 : ℝ)^n ≤
      1/(2000*Real.sqrt (n:ℝ)) := by
    have hpn : (39/40 : ℝ)^n ≤ 1/(4*(n:ℝ)^2) := by
      apply (le_div_iff₀ (by positivity : (0:ℝ)<4*(n:ℝ)^2)).2
      nlinarith [hplatform0]
    have hnsq : 500*Real.sqrt (n:ℝ) ≤ (n:ℝ)^2 := by
      nlinarith [hrootn_le_n, mul_nonneg (show (0:ℝ) ≤ n-500 by linarith)
        (show (0:ℝ) ≤ n by linarith)]
    have hfrac : 1/(4*(n:ℝ)^2) ≤ 1/(2000*Real.sqrt (n:ℝ)) := by
      apply (div_le_div_iff₀ (by positivity : (0:ℝ)<4*(n:ℝ)^2)
        (by positivity : (0:ℝ)<2000*Real.sqrt (n:ℝ))).2
      nlinarith [hnsq]
    exact hpn.trans hfrac
  have hG := gaussian_model_factor_lt n hn
  have hcat0 := normalizedCatalanOddMoment_nonneg (k-1)
  have hcatsq := normalizedCatalanOddMoment_square_lower (k-1)
  have hcast : ((k-1:ℕ):ℝ)+1 = (k:ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    ring
  rw [hcast] at hcatsq
  have hcomp : (1411^2 : ℝ)*(k:ℝ) < 1000^2*(n:ℝ) := by
    rw [hnform]
    nlinarith
  have htargetSq : ((1411/2000 : ℝ)/Real.sqrt n)^2 <
      (normalizedCatalanOddMoment (k-1))^2 := by
    have hthr : ((1411/2000 : ℝ)/Real.sqrt n)^2 =
        (1411^2 : ℝ)/(2000^2*(n:ℝ)) := by
      rw [div_pow, Real.sq_sqrt hn0.le]
      ring
    rw [hthr]
    have hlower : (1411^2 : ℝ)/(2000^2*(n:ℝ)) < 1/(4*(k:ℝ)) := by
      apply (div_lt_div_iff₀ (by positivity : (0:ℝ)<2000^2*(n:ℝ))
        (by positivity : (0:ℝ)<4*(k:ℝ))).2
      nlinarith [hcomp]
    have hcatLower : 1/(4*(k:ℝ)) ≤
        (normalizedCatalanOddMoment (k-1))^2 := by
      apply (div_le_iff₀ (by positivity : (0:ℝ)<4*(k:ℝ))).2
      nlinarith [hcatsq]
    exact hlower.trans_le hcatLower
  have htarget : (1411/2000 : ℝ)/Real.sqrt n <
      normalizedCatalanOddMoment (k-1) := by
    have ht0 : 0 ≤ (1411/2000 : ℝ)/Real.sqrt n := by positivity
    nlinarith
  change (39/40 : ℝ)^n +
    Real.sqrt (Real.pi / ((n:ℝ)*(8/5)/Real.pi^2)) /
      (2*Real.pi) < normalizedCatalanOddMoment (k-1)
  calc
    _ < 1/(2000*Real.sqrt (n:ℝ)) +
        (141/200 : ℝ)/Real.sqrt n :=
      add_lt_add_of_le_of_lt hplatform hG
    _ = (1411/2000 : ℝ)/Real.sqrt n := by ring
    _ < normalizedCatalanOddMoment (k-1) := htarget

end SpringerLean

#print axioms SpringerLean.gaussian_model_factor_lt
#print axioms SpringerLean.gaussian_platform_lt_normalizedCatalan
