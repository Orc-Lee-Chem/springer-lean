import SpringerLean.Round1999OddStarBoundaryFactorDerivative
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace SpringerLean

/-- Radial coordinate of the explicit odd-star seed boundary at angle θ. -/
noncomputable def oddStarBoundaryRadius (m : ℕ) (θ : ℝ) : ℝ :=
  (2 + 2 * Real.cos θ) ^ ((m : ℝ)⁻¹)

/-- The moving mth-root boundary parametrization used in the odd
first-variation calculation. -/
noncomputable def oddStarMovingBoundaryPoint (m : ℕ) (r : ℝ)
    (θ t : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp
    (((m : ℂ)⁻¹) * Complex.log
      (oddStarBoundaryFactor (Complex.exp ((θ : ℂ) * Complex.I)) t))

theorem oddStarMovingBoundaryPoint_hasDerivAt_zero
    (m : ℕ) (r θ : ℝ) :
    HasDerivAt (oddStarMovingBoundaryPoint m r θ)
      ((r : ℂ) * (m : ℂ)⁻¹ *
        ((Real.sin θ : ℂ) + (Real.cos θ - 1 : ℝ) * Complex.I)) 0 := by
  have hlog := oddStarBoundaryFactor_log_hasDerivAt_angle θ
  have hscaled := hlog.const_mul (m : ℂ)⁻¹
  have hexp := hscaled.cexp
  have hpoint := hexp.const_mul (r : ℂ)
  convert hpoint using 1
  · funext t
    rfl
  · simp [oddStarBoundaryFactor]
    ring

/-- First variation of the manuscript's explicit boundary point Z_t,
with its actual radial coordinate r(θ). -/
theorem oddStarMovingBoundaryPoint_actualRadius_hasDerivAt_zero
    (m : ℕ) (θ : ℝ) :
    HasDerivAt (oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ)
      (((oddStarBoundaryRadius m θ : ℝ) : ℂ) * (m : ℂ)⁻¹ *
        ((Real.sin θ : ℂ) + (Real.cos θ - 1 : ℝ) * Complex.I)) 0 :=
  oddStarMovingBoundaryPoint_hasDerivAt_zero m (oddStarBoundaryRadius m θ) θ

end SpringerLean

#print axioms SpringerLean.oddStarMovingBoundaryPoint_actualRadius_hasDerivAt_zero
