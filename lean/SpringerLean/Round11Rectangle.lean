import SpringerLean.Round11Flux
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

open MeasureTheory

namespace SpringerLean

/-- Rectangular flux needs angular endpoint equality only on the radial
interval that is actually integrated. This avoids imposing global
regularity on the exterior map at unrelated parameter values. -/
theorem periodic_rectangle_flux_local
    (f g : ℝ × ℝ → ℝ)
    (f' g' : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
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
    (hperiodic : ∀ r ∈ Set.Icc r₀ r₁, g (r, θ₁) = g (r, θ₀)) :
    (∫ p in Set.Icc (r₀, θ₀) (r₁, θ₁),
      f' p (1, 0) + g' p (0, 1) ∂volume) =
      (∫ θ in θ₀..θ₁, f (r₁, θ) ∂volume) -
        (∫ θ in θ₀..θ₁, f (r₀, θ) ∂volume) := by
  have hgreen := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    f g f' g' (r₀, θ₀) (r₁, θ₁) ⟨hr, hθ⟩
    hfcont hgcont hfder hgder hint
  have hgeq :
      (∫ r in r₀..r₁, g (r, θ₁) ∂volume) =
        (∫ r in r₀..r₁, g (r, θ₀) ∂volume) := by
    apply intervalIntegral.integral_congr
    intro r hrmem
    exact hperiodic r (by simpa [Set.uIcc_of_le hr] using hrmem)
  rw [hgeq, sub_self, zero_add] at hgreen
  exact hgreen

end SpringerLean
