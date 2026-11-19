import SpringerLean.Round1788ActualAlignedFarPhaseCost

open scoped ComplexConjugate

namespace SpringerLean

/-- Full actual aligned pointwise comparison, combining the near
phase penalty and far unsigned lower-power branches. -/
theorem actualSignedPhaseDensity_aligned_le_twoPower
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd : 0 < 2-‖P‖) (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hW : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P < 1/2)
    (beta v : ℂ) (hvunit : ‖v‖=1) (hphase : (beta*v^k)^2=1)
    (δ : ℝ) (hv : v=(P/(‖P‖ : ℂ))*Complex.exp ((δ : ℂ)*Complex.I))
    (hδ : |(k : ℝ)*δ| ≤ Real.pi/3)
    (z : ℂ) (hz : ‖z‖ < 1) (hx : (9/5 : ℝ) ≤ (conj v*actualHarmonic F z).re)
    (a : ℝ) (ha : 6 ≤ a)
    (hay : a*(((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P) ≤ 3) :
    actualSignedPhaseDensity F k beta z ≤
      twoPowerPhaseTest (2*(1-a/((2*k-2 : ℕ) : ℝ))) (2*k-12)
        ((conj v*actualHarmonic F z).re)/(2 : ℝ)^(2*k-2) := by
  have hi : 2*k-12+10=2*k-2 := by omega
  have hi' : 2*k-12+2=2*k-10 := by omega
  have hfirst : (max ((conj v*actualHarmonic F z).re) 0)^(2*k-2) ≤
      twoPowerPhaseTest (2*(1-a/((2*k-2 : ℕ) : ℝ))) (2*k-12)
        ((conj v*actualHarmonic F z).re) := by
    unfold twoPowerPhaseTest
    rw [hi, hi']
    exact le_max_left _ _
  have hsecond : (2*(1-a/((2*k-2 : ℕ) : ℝ)))^8*
      (max ((conj v*actualHarmonic F z).re) 0)^(2*k-10) ≤
      twoPowerPhaseTest (2*(1-a/((2*k-2 : ℕ) : ℝ))) (2*k-12)
        ((conj v*actualHarmonic F z).re) := by
    unfold twoPowerPhaseTest
    rw [hi, hi']
    exact le_max_right _ _
  by_cases hs : ((2*k-2 : ℕ) : ℝ)*(1-(conj v*actualHarmonic F z).re/2) ≤ 7*a/5
  · exact (actualSignedPhaseDensity_aligned_near_le_projection F hc k hk P hP hd ht hW
      beta v hvunit hphase δ hv hδ z hz hx a hay hs).trans
        (div_le_div_of_nonneg_right hfirst (by positivity))
  · have hfar := actualSignedPhaseDensity_aligned_far_lt_lower_power F hc k hk P hP hd ht hW
      beta v hvunit δ hv hδ z hz hx a ha (le_of_lt (lt_of_not_ge hs))
    exact hfar.le.trans (div_le_div_of_nonneg_right hsecond (by positivity))

end SpringerLean

#print axioms SpringerLean.actualSignedPhaseDensity_aligned_le_twoPower
