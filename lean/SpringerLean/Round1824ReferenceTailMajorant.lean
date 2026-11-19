import SpringerLean.Round1820ReferenceTailIdentity
import SpringerLean.Round1823ReflectedTailMoments

namespace SpringerLean
set_option maxHeartbeats 900000

/-- On the support of the excess, replace the square-root density and
the two-power difference by two polynomial exponential moments. -/
theorem reference_tail_pointwise_majorant
    {a m c x : ℝ} (ha : 0 < a) (hm : 0 < m) (hc : 0 < c)
    (hrel : a+m*c=m) (hx0 : 0 ≤ x) (hxc : x ≤ c) (ell : ℕ) :
    Real.sqrt (1-x^2)*(x^ell*(c^8-x^8)) ≤
      (8*c^(ell+7)*Real.sqrt (2/m))*
        ((Real.sqrt a*(c-x)+m/(2*Real.sqrt a)*(c-x)^2)*
          Real.exp (-(((ell : ℝ)/c)*(c-x)))) := by
  let s := a+m*(c-x)
  have hcx : 0 ≤ c-x := sub_nonneg.mpr hxc
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hscale : (2/m)*s=2*(1-x) := by
    dsimp [s]
    have heq : a+m*(c-x)=m*(1-x) := by nlinarith
    rw [heq]
    field_simp
  have hsquare : 1-x^2 ≤ (2/m)*s := by rw [hscale]; nlinarith [sq_nonneg (1-x)]
  have hroot := Real.sqrt_le_sqrt hsquare
  rw [Real.sqrt_mul (show 0 ≤ 2/m by positivity)] at hroot
  have htangent := sqrt_tail_tangent_bound ha hs
  have hrootT : Real.sqrt (1-x^2) ≤
      Real.sqrt (2/m)*(Real.sqrt a+m*(c-x)/(2*Real.sqrt a)) := by
    have hh := mul_le_mul_of_nonneg_left htangent (Real.sqrt_nonneg (2/m))
    dsimp [s] at hh
    have heq : (a+m*(c-x)-a)/(2*Real.sqrt a)=m*(c-x)/(2*Real.sqrt a) := by ring
    rw [heq] at hh
    exact hroot.trans hh
  have hpower := power_excess_exponential_bound hc hx0 hxc ell
  have hexp : -((ell : ℝ)*(c-x)/c) = -(((ell : ℝ)/c)*(c-x)) := by ring
  rw [hexp] at hpower
  have hnonneg : 0 ≤ x^ell*(c^8-x^8) := by
    apply mul_nonneg (pow_nonneg hx0 _)
    exact sub_nonneg.mpr (pow_le_pow_left₀ hx0 hxc _)
  have hupper : 0 ≤ Real.sqrt (2/m)*(Real.sqrt a+m*(c-x)/(2*Real.sqrt a)) := by positivity
  have hh := mul_le_mul hrootT hpower hnonneg hupper
  exact hh.trans_eq (by ring)

end SpringerLean

#print axioms SpringerLean.reference_tail_pointwise_majorant
