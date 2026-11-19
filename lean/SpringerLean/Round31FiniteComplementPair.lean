import SpringerLean.Round31PairAverage

open MeasureTheory Set Metric

namespace SpringerLean

/-- The actual finite complement circle average as paired upper and lower semicircles. -/
theorem regularVerticalFiniteComplement_circleAverage_eq_angle_pair
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (E : Set ℝ) (hEm : MeasurableSet E)
    (a h T ρ : ℝ) (hh : 0 < h) (hT : h ≤ T)
    (hρ : 0 < ρ) (hρh : ρ < h) :
    Real.circleAverage
      (fun z : ℂ => regularVerticalFiniteComplement F s ξ z.re h T z.im E)
      (a : ℂ) ρ =
      (2 * Real.pi)⁻¹ *
        ∫ θ in (0 : ℝ)..Real.pi,
          (regularVerticalFiniteComplement F s ξ
            (a + ρ * Real.cos θ) h T (ρ * Real.sin θ) E +
           regularVerticalFiniteComplement F s ξ
            (a + ρ * Real.cos θ) h T (-(ρ * Real.sin θ)) E) := by
  let q : ℂ → ℝ := fun z => regularVerticalFiniteComplement F s ξ z.re h T z.im E
  have hci : CircleIntegrable q (a : ℂ) ρ :=
    regularVerticalFiniteComplement_circleIntegrable F hc hs0 hs1 ξ hξ
      E hEm a h T ρ hh hT hρ hρh
  rw [circleAverage_real_center_eq_angle_pair q a ρ hci]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hre (φ : ℝ) : (circleMap (a : ℂ) ρ φ).re = a + ρ * Real.cos φ := by
    rw [show circleMap (a : ℂ) ρ φ = (a : ℂ) + circleMap 0 ρ φ from by
      simp [circleMap]]
    simp [Complex.add_re, circleMap_zero_re]
  have him (φ : ℝ) : (circleMap (a : ℂ) ρ φ).im = ρ * Real.sin φ := by
    rw [show circleMap (a : ℂ) ρ φ = (a : ℂ) + circleMap 0 ρ φ from by
      simp [circleMap]]
    simp [Complex.add_im, circleMap_zero_im]
  dsimp [q]
  rw [hre θ, him θ, hre (-θ), him (-θ)]
  simp only [Real.cos_neg, Real.sin_neg, mul_neg]

end SpringerLean