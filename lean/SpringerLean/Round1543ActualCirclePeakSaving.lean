import SpringerLean.Round1542PeakCircleAverageLoss

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- Every actual full-hull cap incurs the same explicit short-arc
circle-moment saving. All coordinates here are unhalved. -/
theorem actualHarmonic_inner_positivePower_peak_saving
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖=1)
    {h d r : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hd : d=2-2*Real.sin h/h) (hd0 : 0 < d)
    (hdsmall : d ≤ 1/1500)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 2*Real.sin h/h)
    (hr0 : 0 < r) (hrband : 1-Real.sqrt d/3 ≤ r)
    (hr1 : r < 1) {m : ℕ} (hm : 2 ≤ m) :
    let v := d-(3/2:ℝ)*(1-r)*Real.sqrt d
    (4/(15*Real.pi):ℝ)*(m:ℝ)*((m:ℝ)-1)*
        (2*r-v)^(m-2)*v^2*Real.sqrt v ≤
      Real.circleAverage
        (fun z : ℂ => (max (2*z.re) 0)^m) 0 r -
      Real.circleAverage
        (fun z => (max ((conj ξ*actualHarmonic F z).re) 0)^m) 0 r := by
  dsimp only
  let v : ℝ := d-(3/2:ℝ)*(1-r)*Real.sqrt d
  let M : ℝ := flattenedCosinePoissonAtReal h r
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hs2 : (Real.sqrt d)^2=d := Real.sq_sqrt hd0.le
  have hmul := mul_le_mul_of_nonneg_right hrband hs
  have hv0 : 0 ≤ v := by dsimp [v]; nlinarith [hmul,hs2]
  have hv1 : v ≤ 1 := by
    dsimp [v]
    have hpos : 0 ≤ (1-r)*Real.sqrt d := by positivity
    nlinarith [hdsmall,hpos]
  have hM0 : 0 ≤ M :=
    flattenedCosinePoissonAtReal_nonneg h hh0 hhpi hr0 hr1
  have hMq : M ≤ 2*r-v := by
    have hp := flattenedCosinePoisson_peak_defect_three_halves
      hh0 hhpi hd hd0 hdsmall hrband hr1
    dsimp [M,v]
    linarith
  have hmodel := clippedTangentPower_peak_circleAverage_loss
    hr0.le hr1.le hv0 hv1 hM0 hMq hm
  have hactual := actualHarmonic_inner_positivePower_le_clippedModel_actual
    F hc ξ hξ h hh0 hhpi hcap hr0 hr1 (by omega : 1 ≤ m)
  dsimp [M] at hmodel
  dsimp [v] at hmodel ⊢
  linarith [hmodel,hactual]

end SpringerLean

#print axioms SpringerLean.actualHarmonic_inner_positivePower_peak_saving
