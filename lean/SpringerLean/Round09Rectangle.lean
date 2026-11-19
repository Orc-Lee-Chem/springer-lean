import SpringerLean.Round09WeightedImage
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

open MeasureTheory

namespace SpringerLean

/-- Rectangular flux with matching angular endpoint values. The angular
boundary terms cancel exactly, leaving outer radial flux minus inner radial
flux. The smooth pullback of the primitive for the weighted-area form will
be inserted as `f` and `g` in a later step. -/
theorem periodic_rectangle_flux
    (f g : ℝ × ℝ → ℝ)
    (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ)
    (r₀ r₁ θ₀ θ₁ : ℝ)
    (hr : r₀ ≤ r₁) (hθ : θ₀ ≤ θ₁)
    (hfcont : ContinuousOn f (Set.Icc (r₀, θ₀) (r₁, θ₁)))
    (hgcont : ContinuousOn g (Set.Icc (r₀, θ₀) (r₁, θ₁)))
    (hfder : ∀ p ∈ Set.Ioo r₀ r₁ ×ˢ Set.Ioo θ₀ θ₁,
      HasFDerivAt f (f' p) p)
    (hgder : ∀ p ∈ Set.Ioo r₀ r₁ ×ˢ Set.Ioo θ₀ θ₁,
      HasFDerivAt g (g' p) p)
    (hint : IntegrableOn (fun p => f' p (1, 0) + g' p (0, 1))
      (Set.Icc (r₀, θ₀) (r₁, θ₁)))
    (hperiodic : ∀ r : ℝ, g (r, θ₁) = g (r, θ₀)) :
    (∫ p in Set.Icc (r₀, θ₀) (r₁, θ₁),
      f' p (1, 0) + g' p (0, 1) ∂volume) =
      (∫ θ in θ₀..θ₁, f (r₁, θ) ∂volume) -
        (∫ θ in θ₀..θ₁, f (r₀, θ) ∂volume) := by
  have hgreen := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    f g f' g' (r₀, θ₀) (r₁, θ₁) ⟨hr, hθ⟩
    hfcont hgcont hfder hgder hint
  have hgeq : (fun r : ℝ => g (r, θ₁)) = fun r => g (r, θ₀) :=
    funext hperiodic
  rw [hgeq, sub_self, zero_add] at hgreen
  exact hgreen

/-- The harmonic filling and the genuine exterior dilate trace literally the
same parametrized unit-circle curve. Consequently their tangential
derivatives agree wherever they are read. -/
theorem regularHarmonic_boundary_curve_eq
    (F : ℂ → ℂ) {s : ℝ} (hs : 0 < s) :
    (fun θ : ℝ =>
      regularHarmonic s F (Complex.exp ((θ : ℂ) * Complex.I))) =
    (fun θ : ℝ =>
      rescaleExterior s F (Complex.exp ((θ : ℂ) * Complex.I))) := by
  funext θ
  exact regularHarmonic_unitCircle_eq_actual F hs
    (Complex.norm_exp_ofReal_mul_I θ)

theorem regularHarmonic_boundary_tangent_eq
    (F : ℂ → ℂ) {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    deriv (fun t : ℝ =>
      regularHarmonic s F (Complex.exp ((t : ℂ) * Complex.I))) θ =
    deriv (fun t : ℝ =>
      rescaleExterior s F (Complex.exp ((t : ℂ) * Complex.I))) θ := by
  rw [regularHarmonic_boundary_curve_eq F hs]

/-- Unit-circle boundary cancellation for any proposed one-form primitive.
The two line integrals use the same curve and the same tangent. -/
theorem regularHarmonic_boundary_circulation_eq
    (F : ℂ → ℂ) {s : ℝ} (hs : 0 < s) (A : ℂ → ℂ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      A (regularHarmonic s F (Complex.exp ((θ : ℂ) * Complex.I))) *
        deriv (fun t : ℝ =>
          regularHarmonic s F (Complex.exp ((t : ℂ) * Complex.I))) θ) =
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      A (rescaleExterior s F (Complex.exp ((θ : ℂ) * Complex.I))) *
        deriv (fun t : ℝ =>
          rescaleExterior s F (Complex.exp ((t : ℂ) * Complex.I))) θ) := by
  exact congrArg
    (fun c : ℝ → ℂ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), A (c θ) * deriv c θ)
    (regularHarmonic_boundary_curve_eq F hs)

end SpringerLean
