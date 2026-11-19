import SpringerLean.Round687LogarithmicProjection
import SpringerLean.Round13Mean

open Metric Set
open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false

/-- Reflection preserves circle means at an arbitrary center. -/
theorem circleAverage_comp_conj_any_center
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (z : ℂ) (ρ : ℝ) :
    Real.circleAverage (fun w : ℂ => f (conj w)) z ρ =
      Real.circleAverage f (conj z) ρ := by
  have heq : (fun w : ℂ => f (conj (w+z))) =
      (fun w : ℂ => (fun v : ℂ => f (v+conj z)) (conj w)) := by
    funext w
    rw [map_add]
  calc
    Real.circleAverage (fun w : ℂ => f (conj w)) z ρ =
        Real.circleAverage (fun w : ℂ => f (conj (w+z))) 0 ρ :=
      Real.circleAverage_map_add_const.symm
    _ = Real.circleAverage (fun w : ℂ => f (w+conj z)) 0 ρ := by
      rw [heq]
      exact circleAverage_comp_conj_zero (fun w : ℂ => f (w+conj z)) ρ
    _ = Real.circleAverage f (conj z) ρ := Real.circleAverage_map_add_const

/-- The positive-angle convention matching actualAngularTopValue. -/
noncomputable def positiveLogActualProjection (F : ℂ → ℂ) (c z : ℂ) : ℝ :=
  logarithmicActualProjection F c (conj z)

theorem positiveLogActualProjection_angle
    (F : ℂ → ℂ) (c : ℂ) (x t : ℝ) :
    positiveLogActualProjection F c ((x : ℂ)+(t : ℂ)*Complex.I) =
      (c*actualHarmonic F (circleMap 0 (Real.exp x) t)).re := by
  have heq : conj ((x : ℂ)+(t : ℂ)*Complex.I) =
      (x : ℂ)+((-t : ℝ) : ℂ)*Complex.I := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
    ring
  rw [positiveLogActualProjection, heq, logarithmicActualProjection_angle, neg_neg]

theorem positiveLogActualProjection_continuousOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ) :
    ContinuousOn (positiveLogActualProjection F c) {z : ℂ | z.re < 0} := by
  change ContinuousOn (fun z : ℂ => logarithmicActualProjection F c (conj z)) _
  apply (logarithmicActualProjection_harmonicOnNhd F hc c).continuousOn.comp
    Complex.continuous_conj.continuousOn
  intro z hz
  simpa only [mem_setOf_eq, Complex.conj_re] using hz

theorem positiveLogActualProjection_circleIntegrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {z : ℂ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρx : ρ < -z.re) :
    CircleIntegrable (positiveLogActualProjection F c) z ρ := by
  apply ((positiveLogActualProjection_continuousOn F hc c).mono ?_).circleIntegrable'
  intro w hw
  have hn : ‖w-z‖ = ρ := by
    simpa only [mem_sphere, dist_eq_norm, abs_of_nonneg hρ0] using hw
  have hre : w.re-z.re ≤ ρ := by
    simpa only [Complex.sub_re, hn] using Complex.re_le_norm (w-z)
  change w.re < 0
  linarith

/-- The SAME actual positive-angle projection has the local harmonic mean.
This is the individual mean needed in the paired-set Fubini argument. -/
theorem positiveLogActualProjection_circleAverage
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {z : ℂ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρx : ρ < -z.re) :
    Real.circleAverage (positiveLogActualProjection F c) z ρ =
      positiveLogActualProjection F c z := by
  change Real.circleAverage (fun w : ℂ => logarithmicActualProjection F c (conj w)) z ρ = _
  rw [circleAverage_comp_conj_any_center]
  exact logarithmicActualProjection_circleAverage F hc c hρ0
    (by simpa only [Complex.conj_re] using hρx)

end SpringerLean

#print axioms SpringerLean.circleAverage_comp_conj_any_center
#print axioms SpringerLean.positiveLogActualProjection_angle
#print axioms SpringerLean.positiveLogActualProjection_continuousOn
#print axioms SpringerLean.positiveLogActualProjection_circleIntegrable
#print axioms SpringerLean.positiveLogActualProjection_circleAverage
