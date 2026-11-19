import SpringerLean.Round81BoundaryPrimitive

namespace SpringerLean

open MeasureTheory

/-- Periodicity turns the Green boundary integral into half the imaginary
part of the complex cross term. This is the real-variable reduction used
before Fourier orthogonality. -/
theorem oriented_boundary_twice_eq_skew_integral
    (X Y : ℝ → ℝ)
    (hX : Differentiable ℝ X) (hY : Differentiable ℝ Y)
    (hX' : Continuous (deriv X)) (hY' : Continuous (deriv Y))
    (hperiod : X (2 * Real.pi) * Y (2 * Real.pi) = X 0 * Y 0) :
    2 * (∫ θ in (0 : ℝ)..(2 * Real.pi), X θ * deriv Y θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        X θ * deriv Y θ - Y θ * deriv X θ := by
  let a : ℝ := 2 * Real.pi
  have hxy : IntervalIntegrable (fun θ => X θ * deriv Y θ) volume 0 a :=
    (hX.continuous.mul hY').intervalIntegrable 0 a
  have hyx : IntervalIntegrable (fun θ => deriv X θ * Y θ) volume 0 a :=
    (hX'.mul hY.continuous).intervalIntegrable 0 a
  have hftc :
      (∫ θ in (0 : ℝ)..a,
        deriv X θ * Y θ + X θ * deriv Y θ) = 0 := by
    have h := intervalIntegral.integral_deriv_mul_eq_sub
      (fun θ _ => (hX θ).hasDerivAt)
      (fun θ _ => (hY θ).hasDerivAt)
      (hX'.intervalIntegrable 0 a) (hY'.intervalIntegrable 0 a)
    simpa only [a, hperiod, sub_self] using h
  rw [intervalIntegral.integral_add hyx hxy] at hftc
  have hskew :
      (∫ θ in (0 : ℝ)..a,
        X θ * deriv Y θ - Y θ * deriv X θ) =
        (∫ θ in (0 : ℝ)..a, X θ * deriv Y θ) -
        (∫ θ in (0 : ℝ)..a, deriv X θ * Y θ) := by
    rw [show (fun θ => X θ * deriv Y θ - Y θ * deriv X θ) =
      (fun θ => X θ * deriv Y θ - deriv X θ * Y θ) from by
        funext θ; ring]
    exact intervalIntegral.integral_sub hxy hyx
  change 2 * (∫ θ in (0 : ℝ)..a, X θ * deriv Y θ) = _
  rw [hskew]
  linarith

end SpringerLean