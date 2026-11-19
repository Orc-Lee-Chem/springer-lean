import SpringerLean.Round1859OddBoundarySecondMoment

namespace SpringerLean

/-- The analytic second-moment part of the even-star factor bound.
The separate hypothesis is exactly the potential-theoretic comparison
to be obtained from the power-map pushforward, PR2 and BLP. -/
theorem evenStar_odd_secondMoment_factor_margin
    (k : ℕ) (hk : 0 < k)
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (hodd : ∀ z ∈ exteriorDisk, G (-z) = -G z)
    (logGap : ℝ)
    (hpotential :
      (2 - actualBoundaryRadialMoment G 2) / (64 * (k : ℝ) ^ 2) ≤ logGap) :
    (1 - ‖exteriorForwardCoeff G 1‖ ^ 2) / (96 * (k : ℝ) ^ 2) ≤ logGap := by
  have hmoment := actualBoundaryRadialMoment_two_odd_margin G hc hodd
  have hkpos : 0 < (64 : ℝ) * (k : ℝ) ^ 2 := by
    positivity
  have hdeficit : (2 / 3 : ℝ) *
      (1 - ‖exteriorForwardCoeff G 1‖ ^ 2) ≤
      2 - actualBoundaryRadialMoment G 2 := by
    linarith
  have hdiv := div_le_div_of_nonneg_right hdeficit hkpos.le
  have hid : ((2 / 3 : ℝ) * (1 - ‖exteriorForwardCoeff G 1‖ ^ 2)) /
      (64 * (k : ℝ) ^ 2) =
      (1 - ‖exteriorForwardCoeff G 1‖ ^ 2) / (96 * (k : ℝ) ^ 2) := by
    ring
  rw [hid] at hdiv
  exact hdiv.trans hpotential

end SpringerLean

#check @SpringerLean.evenStar_odd_secondMoment_factor_margin
#print axioms SpringerLean.evenStar_odd_secondMoment_factor_margin
