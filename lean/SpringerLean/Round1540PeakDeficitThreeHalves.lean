import SpringerLean.Round1539PoissonTailMass

open MeasureTheory Set

namespace SpringerLean
set_option maxHeartbeats 640000

private theorem small_cap_angle_cost
    {h d : ℝ} (hh0 : 0 < h) (hd0 : 0 < d)
    (hlo : Real.sqrt d ≤ h) (hhi : h ≤ (7/4)*Real.sqrt d) :
    h+d/h ≤ (65/28)*Real.sqrt d := by
  let s := Real.sqrt d
  have hs0 : 0 < s := Real.sqrt_pos.2 hd0
  have hs2 : s^2=d := Real.sq_sqrt hd0.le
  have hlo' : (4/7:ℝ)*s ≤ h := by dsimp [s] at *; nlinarith
  have hhi' : h ≤ (7/4:ℝ)*s := hhi
  have hprod : (h-(7/4:ℝ)*s)*(h-(4/7:ℝ)*s) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hpoly : h^2+d ≤ (65/28:ℝ)*s*h := by
    nlinarith [hprod,hs2]
  have hdiv : (d/h)*h=d := div_mul_cancel₀ d (ne_of_gt hh0)
  nlinarith [hpoly,hdiv]

private theorem small_cap_numeric_cost
    {h d r : ℝ} (hh0 : 0 < h) (hd0 : 0 < d)
    (hdsmall : d ≤ 1/1500)
    (hlo : Real.sqrt d ≤ h) (hhi : h ≤ (7/4)*Real.sqrt d)
    (hrband : 1-Real.sqrt d/3 ≤ r) (hr1 : r < 1) :
    (1-r^2)/(Real.pi*r)*(h+d/h) ≤
      (3/2:ℝ)*(1-r)*Real.sqrt d := by
  let s := Real.sqrt d
  have hs0 : 0 < s := Real.sqrt_pos.2 hd0
  have hs2 : s^2=d := Real.sq_sqrt hd0.le
  have hsmax : s ≤ 3/100 := by
    dsimp [s] at *
    nlinarith [hs2]
  have hrmin : (99/100:ℝ) ≤ r := by
    dsimp [s] at *
    nlinarith [hrband,hsmax]
  have hr0 : 0 < r := by linarith
  have hπlow : (25/8:ℝ) ≤ Real.pi := by
    have hp := Real.pi_gt_d2
    norm_num at hp ⊢
    linarith
  have hπr : 0 < Real.pi*r := mul_pos Real.pi_pos hr0
  have hπrLower : (25/8:ℝ)*r ≤ Real.pi*r :=
    mul_le_mul_of_nonneg_right hπlow hr0.le
  have hscaled := mul_le_mul_of_nonneg_left hπrLower
    (show 0 ≤ (199/99:ℝ)*(8/25) by norm_num)
  have hcoef : (1+r)/(Real.pi*r) ≤ (199/99:ℝ)*(8/25) := by
    apply (div_le_iff₀ hπr).2
    nlinarith [hscaled,hrmin]
  have hcoefFinal : (1+r)/(Real.pi*r)*(65/28:ℝ) ≤ 3/2 := by
    have hn : (199/99:ℝ)*(8/25)*(65/28) < 3/2 := by norm_num
    nlinarith [hcoef]
  have hcost := small_cap_angle_cost hh0 hd0 hlo hhi
  have hrawcoef : 0 ≤ (1-r^2)/(Real.pi*r) := by
    have : 0 ≤ 1-r^2 := by nlinarith
    positivity
  have hmulCost := mul_le_mul_of_nonneg_left hcost hrawcoef
  have hmulCoef := mul_le_mul_of_nonneg_left hcoefFinal
    (show 0 ≤ (1-r)*s by positivity)
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hπne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hfactor : (1-r^2)/(Real.pi*r)*((65/28:ℝ)*s) =
      (1-r)*s*((1+r)/(Real.pi*r)*(65/28)) := by
    field_simp
    ring
  rw [hfactor] at hmulCost
  dsimp [s] at *
  nlinarith [hmulCost,hmulCoef]

/-- Quantitative peak deficit on the radial band used by the thin-annulus
saving. This version keeps the sharper 3/2 constant. -/
theorem flattenedCosinePoisson_peak_defect_three_halves
    {h d r : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hd : d=2-2*Real.sin h/h) (hd0 : 0 < d)
    (hdsmall : d ≤ 1/1500)
    (hrband : 1-Real.sqrt d/3 ≤ r) (hr1 : r < 1) :
    d-(3/2:ℝ)*(1-r)*Real.sqrt d ≤
      2*r-flattenedCosinePoissonAtReal h r := by
  have hr0 : 0 < r := by
    have hs2 := Real.sq_sqrt hd0.le
    have hs0 := Real.sqrt_nonneg d
    have hsmax : Real.sqrt d ≤ 3/100 := by nlinarith [hs2]
    linarith
  have hangle := small_flattened_arc_sqrt_bounds hh0 hhpi hd hd0 hdsmall
  have hsqrt : Real.sqrt d ≤ Real.sqrt (3*d) :=
    Real.sqrt_le_sqrt (by nlinarith [hd0.le])
  have hlo : Real.sqrt d ≤ h := hsqrt.trans hangle.1
  have hcost := small_cap_numeric_cost hh0 hd0 hdsmall hlo hangle.2 hrband hr1
  have hA0 : 0 ≤ flattenedCapPoissonMass h r := by
    dsimp [flattenedCapPoissonMass]
    apply mul_nonneg (by positivity)
    apply setIntegral_nonneg measurableSet_Ioc
    intro θ _
    exact (centeredPoisson_weight_bounds hr0 hr1 θ).1
  have htail := flattenedCapPoissonMass_tail_le hh0 hhpi hr0 hr1
  have htailD := mul_le_mul_of_nonneg_left htail hd0.le
  have htailNorm : d*((1-r^2)/(Real.pi*r*h)) =
      d*(1-r^2)/(Real.pi*r*h) := by ring
  rw [htailNorm] at htailD
  have hformula := flattenedCosinePoisson_peak_defect_exact
    hh0 hhpi hr0 hr1
  dsimp only at hformula
  rw [←hd] at hformula
  have hterm : 0 ≤ ((1-r)^2/r)*flattenedCapPoissonMass h r := by
    positivity
  have hhne : h ≠ 0 := ne_of_gt hh0
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hπne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hcostEq : d*(1-r^2)/(Real.pi*r*h)+
      (1-r^2)*h/(Real.pi*r) =
      (1-r^2)/(Real.pi*r)*(h+d/h) := by
    field_simp
    ring
  calc
    d-(3/2:ℝ)*(1-r)*Real.sqrt d ≤
        d-(1-r^2)/(Real.pi*r)*(h+d/h) := by linarith [hcost]
    _ = d-(d*(1-r^2)/(Real.pi*r*h)+
        (1-r^2)*h/(Real.pi*r)) := by rw [hcostEq]
    _ ≤ d-(d*(1-flattenedCapPoissonMass h r)+
        (1-r^2)*h/(Real.pi*r)) := by nlinarith [htailD]
    _ ≤ 2*r-flattenedCosinePoissonAtReal h r := by
      rw [hformula]
      nlinarith [hterm]

/-- The peak deficit is at least d/2 and therefore strictly positive. -/
theorem flattenedCosinePoisson_peak_defect_positive
    {h d r : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hd : d=2-2*Real.sin h/h) (hd0 : 0 < d)
    (hdsmall : d ≤ 1/1500)
    (hrband : 1-Real.sqrt d/3 ≤ r) (hr1 : r < 1) :
    d/2 ≤ 2*r-flattenedCosinePoissonAtReal h r ∧
      0 < 2*r-flattenedCosinePoissonAtReal h r := by
  have hv := flattenedCosinePoisson_peak_defect_three_halves
    hh0 hhpi hd hd0 hdsmall hrband hr1
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hs2 : (Real.sqrt d)^2=d := Real.sq_sqrt hd0.le
  have hmul := mul_le_mul_of_nonneg_right hrband hs
  constructor <;> nlinarith [hmul,hs2]

end SpringerLean

#print axioms SpringerLean.flattenedCosinePoisson_peak_defect_three_halves
#print axioms SpringerLean.flattenedCosinePoisson_peak_defect_positive
