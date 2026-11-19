import SpringerLean.Round1530ShortPeakArcIntegral

namespace SpringerLean
set_option maxHeartbeats 320000

/-- The clipped-power loss on the explicit arc 0≤θ≤√v. The angular
bound uses only `2(1-cos θ)≤θ²` and r≤1. -/
theorem clippedTangentPower_shortPeakArc_pointwise
    {r v M θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hv : 0 ≤ v) (hM : 0 ≤ M)
    (hMq : M ≤ 2*r-v) (hθ0 : 0 ≤ θ)
    (hθv : θ ≤ Real.sqrt v) {m : ℕ} (hm : 2 ≤ m) :
    ((m:ℝ)*((m:ℝ)-1)/2)*(2*r-v)^(m-2)*(v-θ^2)^2 ≤
      (max (2*r*Real.cos θ) 0)^m -
        clippedTangentPower M m (2*r*Real.cos θ) := by
  let q := 2*r-v
  let x := 2*r*Real.cos θ
  have hq : 0 ≤ q := hM.trans hMq
  have hθsq : θ^2 ≤ v := by
    have hroot : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
    nlinarith [Real.sq_sqrt hv]
  have hcos0 : 0 ≤ 1-Real.cos θ := by linarith [Real.cos_le_one θ]
  have hcos : 2*(1-Real.cos θ) ≤ θ^2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := θ)]
  have hdrop : 2*r*(1-Real.cos θ) ≤ θ^2 := by
    have hp := mul_le_mul_of_nonneg_right hr1 hcos0
    nlinarith [hp,hcos]
  have hdelta : v-θ^2 ≤ x-q := by
    dsimp [x,q]
    nlinarith [hdrop]
  have hdelta0 : 0 ≤ v-θ^2 := sub_nonneg.mpr hθsq
  have hqx : q ≤ x := by linarith
  have hgap := clippedTangentPower_quadratic_gap hM hMq hqx hm
  have hsquare : (v-θ^2)^2 ≤ (x-q)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdelta)
      (add_nonneg hdelta0 (sub_nonneg.mpr hqx))]
  have hcoef : 0 ≤ ((m:ℝ)*((m:ℝ)-1)/2)*q^(m-2) := by
    have hmreal : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
    positivity
  have hmul := mul_le_mul_of_nonneg_left hsquare hcoef
  dsimp [q,x] at *
  nlinarith [hgap,hmul]

end SpringerLean

#print axioms SpringerLean.clippedTangentPower_shortPeakArc_pointwise
