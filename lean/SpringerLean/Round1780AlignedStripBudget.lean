import SpringerLean.Round1777AlignedAngularScalar

namespace SpringerLean
set_option maxHeartbeats 500000

/-- The rotated strip's transverse quadratic has a uniform small
linear coefficient. This is independent of any phase enumeration. -/
theorem aligned_strip_quadratic_coarse
    {y Q s τ : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2)
    (hQ : 0 ≤ Q) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 7/5000)
    (hstrip : Q^2 ≤ 4*y*(y+2*s+Q*τ)) :
    Q^2 ≤ 1+8*y*s+(7/2500 : ℝ)*Q := by
  have hy2 : y^2 ≤ 1/4 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hy1 (mul_nonneg hQ hτ0)
  have h2 := mul_le_mul_of_nonneg_left hτ1 hQ
  nlinarith

theorem aligned_strip_near_angle
    {k : ℕ} (hk : 751 ≤ k) {y Q s a H : ℝ}
    (hy0 : 0 ≤ y) (hQ : 0 ≤ Q) (hH0 : 0 ≤ H)
    (hquad : Q^2 ≤ 1+8*y*s+(7/2500 : ℝ)*Q)
    (hs : s ≤ 7*a/5) (hay : a*y ≤ 3)
    (hH : H ≤ 21/10+(4/7 : ℝ)*Q) :
    (k : ℝ)*H/((2*k-2 : ℕ) : ℝ) < 14/5 := by
  have hk' : (751 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : ((2*k-2 : ℕ) : ℝ)=2*(k : ℝ)-2 := by
    have hh : 2 ≤ 2*k := by omega
    rw [Nat.cast_sub hh, Nat.cast_mul, Nat.cast_ofNat]
  have hys : y*s ≤ 21/5 := by
    have hh := mul_le_mul_of_nonneg_left hs hy0
    nlinarith
  have hQ6 : Q < 6 := by
    by_contra hh
    have hh' : 6 ≤ Q := le_of_not_gt hh
    have hp := mul_nonneg hQ (sub_nonneg.mpr hh')
    nlinarith
  have hHbound : H < 387/70 := by linarith
  rw [hm]
  apply (div_lt_iff₀ (by linarith : 0 < 2*(k : ℝ)-2)).mpr
  have hh := mul_lt_mul_of_pos_left hHbound (by linarith : (0 : ℝ) < k)
  nlinarith

/-- A rational quadratic completion replaces the far-region square-root
root bound and its derivative calculation. -/
theorem aligned_strip_far_cost
    {y Q s a H : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2)
    (hQ : 0 ≤ Q) (hs0 : 0 ≤ s) (ha : 6 ≤ a) (hs : 7*a/5 ≤ s)
    (hH0 : 0 ≤ H) (hH : H ≤ 21/10+(4/7 : ℝ)*Q)
    (hquad : Q^2 ≤ 1+8*y*s+(7/2500 : ℝ)*Q) :
    H^2/2 < 8*(s-a) := by
  have hys : 0 ≤ y*s := mul_nonneg hy0 hs0
  have hQlinear : Q ≤ 1+Q^2/4 := by nlinarith [sq_nonneg (Q-2)]
  have hQ2 : Q^2 ≤ (51/50 : ℝ)*(1+8*y*s) := by nlinarith
  have hHmax0 : 0 ≤ 21/10+(4/7 : ℝ)*Q := by positivity
  have hH2 : H^2 ≤ (21/10+(4/7 : ℝ)*Q)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hH) (add_nonneg hHmax0 hH0)]
  have hcost : H^2/2 ≤ 11/2+(7/3 : ℝ)*y*s := by
    nlinarith [sq_nonneg (Q-49/10)]
  have hys1 := mul_le_mul_of_nonneg_right hy1 hs0
  nlinarith

end SpringerLean

#print axioms SpringerLean.aligned_strip_near_angle
#print axioms SpringerLean.aligned_strip_far_cost
