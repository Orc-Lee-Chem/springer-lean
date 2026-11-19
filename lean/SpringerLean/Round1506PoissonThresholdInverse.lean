import SpringerLean.Round1505FlattenedMean

namespace SpringerLean

/-- In the proper range, the cosine threshold parameter recovers the
original Poisson threshold exactly. -/
theorem centeredPoisson_threshold_eq_of_cosine_parameter
    {r t q : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ht : 0 < t)
    (ha : 2*Real.cos q = ((1+r^2)*t-(1-r^2))/(r*t)) :
    t = poissonKernel 0 (r:ℂ) (circleMap 0 1 q) := by
  have hrt : 0 < r*t := mul_pos hr0 ht
  have hden := centeredPoissonDenominator_pos hr0 hr1 q
  have hnum : t*(1+r^2-2*r*Real.cos q)=1-r^2 := by
    have hc := (eq_div_iff hrt.ne').mp ha
    nlinarith
  rw [poissonKernel_centered_cosine_formula hr0.le hr1]
  exact (eq_div_iff hden.ne').mpr hnum

end SpringerLean

#print axioms SpringerLean.centeredPoisson_threshold_eq_of_cosine_parameter
