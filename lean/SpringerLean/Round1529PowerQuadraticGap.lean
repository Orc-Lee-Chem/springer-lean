import SpringerLean.Round1528PoissonArcDefectIntegral

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The first three terms in the binomial expansion, proved uniformly in
the exponent so that no finite list of powers is needed. -/
private theorem pow_quadratic_lower {q t : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t)
    (m : ℕ) (hm : 2 ≤ m) :
    q^m + (m:ℝ)*q^(m-1)*t +
      ((m:ℝ)*((m:ℝ)-1)/2)*q^(m-2)*t^2 ≤ (q+t)^m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num; ring_nf; exact le_rfl
  | succ m hm ih =>
    have hm1 : m + 1 - 1 = m := by omega
    have hm2 : m + 1 - 2 = m - 1 := by omega
    have hm3 : m - 2 + 1 = m - 1 := by omega
    have hmul := mul_le_mul_of_nonneg_left ih (by linarith : 0 ≤ q+t)
    have hmreal : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
    have hlast : 0 ≤ ((m:ℝ)*((m:ℝ)-1)/2)*q^(m-2)*t^3 := by
      positivity
    have hpow1 : q^(m-2)*q = q^(m-1) := by
      rw [←pow_succ, ←hm3]
    have hpow2 : q^(m-1)*q = q^m := by
      rw [←pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    have hpow3 : q^m*q = q^(m+1) := by rw [←pow_succ]
    have hpow4 : (q+t)^m*(q+t)=(q+t)^(m+1) := by rw [←pow_succ]
    simp only [hm1,hm2] at hmul ⊢
    have hexact :
        q^(m+1) + ((m+1:ℕ):ℝ)*q^m*t +
          (((m+1:ℕ):ℝ)*(((m+1:ℕ):ℝ)-1)/2)*q^(m-1)*t^2 +
          ((m:ℝ)*((m:ℝ)-1)/2)*q^(m-2)*t^3 =
        (q^m+(m:ℝ)*q^(m-1)*t+
          ((m:ℝ)*((m:ℝ)-1)/2)*q^(m-2)*t^2)*(q+t) := by
      push_cast
      linear_combination hpow3 - (m:ℝ)*t*hpow2 -
        ((m:ℝ)*((m:ℝ)-1)/2)*t^2*hpow1
    calc
      q^(m+1) + ((m+1:ℕ):ℝ)*q^m*t +
          (((m+1:ℕ):ℝ)*(((m+1:ℕ):ℝ)-1)/2)*q^(m-1)*t^2
          ≤ (q^m+(m:ℝ)*q^(m-1)*t+
              ((m:ℝ)*((m:ℝ)-1)/2)*q^(m-2)*t^2)*(q+t) := by
            linarith [hexact,hlast]
      _ ≤ (q+t)^m*(q+t) := by nlinarith [hmul]
      _ = (q+t)^(m+1) := hpow4

/-- Moving the tangent contact from M to q raises its value at x≥q. -/
theorem powerTangent_mono_contact {M q x : ℝ}
    (hM : 0 ≤ M) (hMq : M ≤ q) (hqx : q ≤ x)
    (m : ℕ) (hm : 1 ≤ m) :
    powerTangent M m x ≤ powerTangent q m x := by
  have hq : 0 ≤ q := hM.trans hMq
  have htq := power_tangent_le hM hq m
  have hp : M^(m-1) ≤ q^(m-1) := by gcongr
  have hdiff : 0 ≤ (m:ℝ)*(q^(m-1)-M^(m-1))*(x-q) := by
    have hmr : (0:ℝ) ≤ m := by positivity
    have hdelta : 0 ≤ x-q := sub_nonneg.mpr hqx
    positivity
  dsimp [powerTangent]
  nlinarith [htq,hdiff]

/-- On x≥q≥M the clipped test loses a quantitative quadratic term. -/
theorem clippedTangentPower_quadratic_gap
    {M q x : ℝ} (hM : 0 ≤ M) (hMq : M ≤ q)
    (hqx : q ≤ x) {m : ℕ} (hm : 2 ≤ m) :
    ((m:ℝ)*((m:ℝ)-1)/2)*q^(m-2)*(x-q)^2 ≤
      (max x 0)^m - clippedTangentPower M m x := by
  have hq : 0 ≤ q := hM.trans hMq
  have hx : 0 ≤ x := hq.trans hqx
  have hrem := pow_quadratic_lower hq (sub_nonneg.mpr hqx) m hm
  have hmono := powerTangent_mono_contact hM hMq hqx m (by omega)
  have hcase : clippedTangentPower M m x ≤ powerTangent M m x := by
    by_cases hMx : M < x
    · exact le_of_eq (clippedTangentPower_eq_tangent hMx m)
    · have hxm : x ≤ M := le_of_not_gt hMx
      have hxeq : x = M := le_antisymm hxm (hMq.trans hqx)
      subst x
      rw [clippedTangentPower_eq_positivePart_pow (le_refl M)]
      simp [powerTangent,max_eq_left hM]
  rw [max_eq_left hx]
  have hrewrite : q+(x-q)=x := by ring
  rw [hrewrite] at hrem
  change clippedTangentPower M m x ≤
    M^m+(m:ℝ)*M^(m-1)*(x-M) at hcase
  dsimp [powerTangent] at hmono ⊢
  nlinarith [hrem,hmono,hcase]

end SpringerLean

#print axioms SpringerLean.powerTangent_mono_contact
#print axioms SpringerLean.clippedTangentPower_quadratic_gap
