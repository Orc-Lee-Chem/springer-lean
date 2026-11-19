import SpringerLean.Round1548ThinAnnulusCircleLower

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- On the outer `sqrt(d)/16` annulus, the actual circle-moment saving
has a fixed positive multiple of `r^(m-2) d^(5/2)`. -/
theorem actualHarmonic_inner_positivePower_thinAnnulus_gain
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖=1)
    {h d r : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hd : d=2-2*Real.sin h/h) (hd0 : 0 < d)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 2*Real.sin h/h)
    {m : ℕ} (hm : 1500 ≤ m) (hD : (m:ℝ)*d ≤ 3/20)
    (hrband : 1-Real.sqrt d/16 ≤ r) (hr1 : r < 1) :
    (9/(50*Real.pi):ℝ)*(m:ℝ)*((m:ℝ)-1)*
        (2*r)^(m-2)*d^2*Real.sqrt d ≤
      Real.circleAverage
        (fun z : ℂ => (max (2*z.re) 0)^m) 0 r -
      Real.circleAverage
        (fun z => (max ((conj ξ*actualHarmonic F z).re) 0)^m) 0 r := by
  let v : ℝ := d-(3/2:ℝ)*(1-r)*Real.sqrt d
  have hb := thinAnnulus_peak_parameter_bounds hm hd0 hD hrband hr1.le
  have hr0 : 0 < r := by dsimp only at hb; linarith [hb.2.2]
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hrband' : 1-Real.sqrt d/3 ≤ r := by nlinarith [hrband,hs]
  have hmR : (1500:ℝ) ≤ m := by exact_mod_cast hm
  have hdsmall : d ≤ 1/1500 := by
    have hp := mul_nonneg (sub_nonneg.mpr hmR) hd0.le
    nlinarith [hD,hp]
  have hactual := actualHarmonic_inner_positivePower_peak_saving
    F hc ξ hξ hh0 hhpi hd hd0 hdsmall hcap
      hr0 hrband' hr1 (by omega : 2 ≤ m)
  dsimp only at hactual
  have hqpow := thinAnnulus_qpow_lower hm hd0 hD hrband hr1.le
  dsimp only at hqpow
  have hvpow := thinAnnulus_five_half_lower hd0 hb.1
  have hv0 : 0 ≤ v := by dsimp [v]; nlinarith [hb.1,hd0]
  have hprod1 := mul_le_mul_of_nonneg_right hqpow
    (show 0 ≤ v^2*Real.sqrt v by positivity)
  have hprod2 := mul_le_mul_of_nonneg_left hvpow
    (show 0 ≤ (9/10:ℝ)*(2*r)^(m-2) by positivity)
  have hprod : (9/10:ℝ)*(2*r)^(m-2)*
      ((3/4:ℝ)*d^2*Real.sqrt d) ≤
      (2*r-v)^(m-2)*(v^2*Real.sqrt v) :=
    hprod2.trans hprod1
  have hA0 : 0 ≤ (4/(15*Real.pi):ℝ)*(m:ℝ)*((m:ℝ)-1) := by
    have hm1 : (1:ℝ) ≤ m := by linarith
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hprod hA0
  dsimp [v] at hactual hscaled
  calc
    (9/(50*Real.pi):ℝ)*(m:ℝ)*((m:ℝ)-1)*
        (2*r)^(m-2)*d^2*Real.sqrt d =
      (4/(15*Real.pi):ℝ)*(m:ℝ)*((m:ℝ)-1)*
        ((9/10:ℝ)*(2*r)^(m-2)*((3/4:ℝ)*d^2*Real.sqrt d)) := by
          ring
    _ ≤ (4/(15*Real.pi):ℝ)*(m:ℝ)*((m:ℝ)-1)*
        ((2*r-(d-(3/2:ℝ)*(1-r)*Real.sqrt d))^(m-2)*
        ((d-(3/2:ℝ)*(1-r)*Real.sqrt d)^2*
          Real.sqrt (d-(3/2:ℝ)*(1-r)*Real.sqrt d))) := by
          simpa only [mul_assoc] using hscaled
    _ ≤ _ := by nlinarith [hactual]

end SpringerLean

#print axioms SpringerLean.actualHarmonic_inner_positivePower_thinAnnulus_gain
