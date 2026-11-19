import SpringerLean.Round679ActualAngularLevels
import SpringerLean.Round39RotateExterior
import Mathlib.Analysis.Complex.Harmonic.MeanValue

open Metric InnerProductSpace
open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false

/-- The reflected actual projection in logarithmic polar coordinates.
The reflection makes this the real part of an analytic function. -/
noncomputable def logarithmicActualProjection (F : ℂ → ℂ) (c z : ℂ) : ℝ :=
  (projectionAnalytic F c (Complex.exp z)).re

theorem logarithmicActualProjection_eq_actual
    (F : ℂ → ℂ) (c z : ℂ) :
    logarithmicActualProjection F c z =
      (c*actualHarmonic F (conj (Complex.exp z))).re := by
  exact (actualHarmonic_projection_reflection F c (Complex.exp z)).symm

theorem logarithmicActualProjection_angle
    (F : ℂ → ℂ) (c : ℂ) (x t : ℝ) :
    logarithmicActualProjection F c ((x : ℂ)+(t : ℂ)*Complex.I) =
      (c*actualHarmonic F (circleMap 0 (Real.exp x) (-t))).re := by
  have hexp : Complex.exp ((x : ℂ)+(t : ℂ)*Complex.I) =
      circleMap 0 (Real.exp x) t := by
    rw [Complex.exp_add, circleMap_zero, Complex.ofReal_exp]
  rw [logarithmicActualProjection_eq_actual, hexp, conj_circleMap_zero]

/-- Harmonicity is proved for the SAME actual F, on the left half-plane;
it is not an input to the future angular optimizer comparison. -/
theorem logarithmicActualProjection_harmonicOnNhd
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ) :
    HarmonicOnNhd (logarithmicActualProjection F c) {z : ℂ | z.re < 0} := by
  intro z hz
  have he : Complex.exp z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right, Complex.norm_exp]
    exact Real.exp_lt_one_iff.mpr hz
  have ha : AnalyticAt ℂ (fun z : ℂ => projectionAnalytic F c (Complex.exp z)) z :=
    (projectionAnalytic_analyticOnNhd F hc c (Complex.exp z) he).comp analyticAt_cexp
  exact ha.harmonicAt_re

private theorem logarithmicProjection_closedBall_subset
    {z : ℂ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < -z.re) :
    closedBall z |ρ| ⊆ {w : ℂ | w.re < 0} := by
  intro w hw
  have hn : ‖w-z‖ ≤ ρ := by
    simpa only [mem_closedBall, dist_eq_norm, abs_of_nonneg hρ0] using hw
  have hre : w.re-z.re ≤ ‖w-z‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (w-z)
  change w.re < 0
  linarith

/-- Circle integrability is kept as an independent interface for the
bounded angular Fubini calculation. No star-function inequality is claimed. -/
theorem logarithmicActualProjection_circleIntegrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {z : ℂ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < -z.re) :
    CircleIntegrable (logarithmicActualProjection F c) z ρ := by
  exact ((logarithmicActualProjection_harmonicOnNhd F hc c).continuousOn.mono
    (sphere_subset_closedBall.trans
      (logarithmicProjection_closedBall_subset hρ0 hρ))).circleIntegrable'

/-- The actual (reflected) projection satisfies equality in the local
circle mean, with radius condition sufficient for the whole closed disk. -/
theorem logarithmicActualProjection_circleAverage
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {z : ℂ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < -z.re) :
    Real.circleAverage (logarithmicActualProjection F c) z ρ =
      logarithmicActualProjection F c z := by
  exact ((logarithmicActualProjection_harmonicOnNhd F hc c).mono
    (logarithmicProjection_closedBall_subset hρ0 hρ)).circleAverage_eq

end SpringerLean
