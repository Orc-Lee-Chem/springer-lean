import SpringerLean.Round2035EvenStarEqualityGeometry

namespace SpringerLean

/-- Exact analytic consequence of the remaining potential comparison.
The comparison is an explicit premise; this is not yet the factor-
constant theorem. -/
theorem evenStar_actual_factor_gap_of_potential_comparison
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ)
    (logGap : ℝ)
    (hpotential :
      (2 - actualBoundaryRadialMoment
        (evenExteriorPowerQuotient F k) 2) /
          (64*(k:ℝ)^2) ≤ logGap) :
    (1 - (k:ℝ)^2*‖exteriorForwardCoeff F (2*k-1)‖^2) /
      (96*(k:ℝ)^2) ≤ logGap := by
  have hmoment := evenExteriorPowerQuotient_secondMoment_original_coeff
    F K k hk hF hK hImage
  have hden : 0 < (64:ℝ)*(k:ℝ)^2 := by positivity
  have hdef : (2/3:ℝ) *
      (1 - (k:ℝ)^2*‖exteriorForwardCoeff F (2*k-1)‖^2) ≤
      2 - actualBoundaryRadialMoment (evenExteriorPowerQuotient F k) 2 := by
    linarith
  have hdiv := div_le_div_of_nonneg_right hdef hden.le
  have hiden : ((2/3:ℝ) *
      (1 - (k:ℝ)^2*‖exteriorForwardCoeff F (2*k-1)‖^2)) /
      (64*(k:ℝ)^2) =
      (1 - (k:ℝ)^2*‖exteriorForwardCoeff F (2*k-1)‖^2) /
        (96*(k:ℝ)^2) := by ring
  rw [hiden] at hdiv
  exact hdiv.trans hpotential

/-- Equality in the comparison's upper bound forces the power-
preimage slit geometry. The potential comparison remains a premise. -/
theorem evenStar_actual_factor_gap_zero_equality_set_of_potential_comparison
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ)
    (logGap : ℝ)
    (hpotential :
      (2 - actualBoundaryRadialMoment
        (evenExteriorPowerQuotient F k) 2) /
          (64*(k:ℝ)^2) ≤ logGap)
    (hzero : logGap = 0) :
    ∃ a : ℂ, ‖a‖ = 1 ∧
      K = {z : ℂ | z^k ∈ (slitMap a '' exteriorDisk)ᶜ} := by
  let G := evenExteriorPowerQuotient F k
  have hG := evenExteriorPowerQuotient_actual_centered
    F K k hk hF hK hImage
  have hnorm : ‖exteriorForwardCoeff G 1‖ ≤ 1 := by
    have hh := exteriorInverseCoeff_one_norm_le G hG
    rwa [exteriorInverseCoeff_one_eq_forwardCoeff_one G hG] at hh
  have hRle : actualBoundaryRadialMoment G 2 ≤ 2 := by
    have hh := actualBoundaryRadialMoment_two_margin G hG
    nlinarith [norm_nonneg (exteriorForwardCoeff G 1)]
  have hden : 0 < (64:ℝ)*(k:ℝ)^2 := by positivity
  have hRge : 2 ≤ actualBoundaryRadialMoment G 2 := by
    have hh : (2-actualBoundaryRadialMoment G 2) /
        (64*(k:ℝ)^2) ≤ 0 := by simpa only [hzero] using hpotential
    have hnum := (div_le_iff₀ hden).mp hh
    linarith
  exact evenPowerQuotient_secondMoment_eq_two_omitted_preimage_slit
    F K k hk hF hK hImage (le_antisymm hRle hRge)

end SpringerLean
