import SpringerLean.Round1896LocalConvexTestTransfer
import Mathlib.Analysis.Convex.Deriv

namespace SpringerLean

/-- The second-derivative estimate in the real-exponent argument can be
proved by showing convexity of the shifted function on the two-unit
parameter interval. This lemma extracts the exact theta(1-theta) loss. -/
theorem interpolation_secant_from_shifted_convex
    (f : ℝ → ℝ) (a L θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hconv : ConvexOn ℝ (Set.Icc a (a + 2))
      (fun x => L / 2 * x ^ 2 - f x)) :
    (1 - θ) * f a + θ * f (a + 2) - f (a + 2 * θ) ≤
      2 * L * θ * (1 - θ) := by
  have ha : a ∈ Set.Icc a (a + 2) := by constructor <;> linarith
  have hb : a + 2 ∈ Set.Icc a (a + 2) := by constructor <;> linarith
  have h := hconv.2 ha hb (by linarith : 0 ≤ 1 - θ) hθ0
    (show 1 - θ + θ = 1 by ring)
  have hpoint : (1 - θ) • a + θ • (a + 2) = a + 2 * θ := by
    simp only [smul_eq_mul]
    ring
  rw [hpoint] at h
  simp only [smul_eq_mul] at h
  nlinarith [sq_nonneg θ]

/-- The first Fourier mode of the projection has amplitude 1+x. Once
that mode is connected to the actual trace, this elementary estimate is
the 3D/8 second-moment correction used in interpolation. -/
theorem interpolation_projection_secondMoment_scalar
    {x E : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hmode : (1 + x) ^ 2 / 8 ≤ E) :
    1 / 2 - E ≤ 3 * (1 - x ^ 2) / 8 := by
  nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]

end SpringerLean

#print axioms SpringerLean.interpolation_secant_from_shifted_convex
#print axioms SpringerLean.interpolation_projection_secondMoment_scalar
