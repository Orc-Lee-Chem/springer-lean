import SpringerLean.Round678AnalyticLevelNull
import SpringerLean.Round14QuadraticPrelude
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory
open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false

/-- The actual inner-circle projection is globally real analytic in the
angle. Reflection is essential: its analytic disk function is the same
projectionAnalytic already used for the verified quadratic test. -/
theorem actualHarmonic_angular_projection_analytic
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    AnalyticOnNhd ℝ
      (fun θ : ℝ => (c*actualHarmonic F (circleMap 0 r θ)).re) Set.univ := by
  intro t _
  have hlin : AnalyticAt ℝ (fun θ : ℝ => -(θ : ℂ)*Complex.I) t :=
    (Complex.ofRealCLM.analyticAt t).neg.mul
      (show AnalyticAt ℝ (fun _ : ℝ => Complex.I) t from analyticAt_const)
  have he : AnalyticAt ℝ Complex.exp (-(t : ℂ)*Complex.I) :=
    analyticAt_cexp.restrictScalars
  have hp : AnalyticAt ℝ (fun θ : ℝ => circleMap 0 r (-θ)) t := by
    have hexp : AnalyticAt ℝ (fun θ : ℝ => Complex.exp (-(θ : ℂ)*Complex.I)) t :=
      he.comp (f := fun θ : ℝ => -(θ : ℂ)*Complex.I) (x := t) hlin
    have hscale : AnalyticAt ℝ
        (fun θ : ℝ => r • Complex.exp (-(θ : ℂ)*Complex.I)) t :=
      (show AnalyticAt ℝ (fun _ : ℝ => r) t from analyticAt_const).smul hexp
    simpa only [circleMap_zero,Complex.ofReal_neg,Algebra.smul_def,
      Complex.coe_algebraMap] using hscale
  have hu : circleMap 0 r (-t) ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball,dist_zero_right,norm_circleMap_zero,abs_of_nonneg hr0] using hr1
  have hJ : AnalyticAt ℝ (projectionAnalytic F c) (circleMap 0 r (-t)) :=
    (projectionAnalytic_analyticOnNhd F hc c _ hu).restrictScalars
  have hreal : AnalyticAt ℝ
      (fun θ : ℝ => (projectionAnalytic F c (circleMap 0 r (-θ))).re) t :=
    (Complex.reCLM.analyticAt _).comp
      (f := fun θ : ℝ => projectionAnalytic F c (circleMap 0 r (-θ))) (x := t)
      (hJ.comp (f := fun θ : ℝ => circleMap 0 r (-θ)) (x := t) hp)
  have hfun : (fun θ : ℝ => (c*actualHarmonic F (circleMap 0 r θ)).re) =
      (fun θ : ℝ => (projectionAnalytic F c (circleMap 0 r (-θ))).re) := by
    funext θ
    simpa only [conj_circleMap_zero,neg_neg] using
      actualHarmonic_projection_reflection F c (circleMap 0 r (-θ))
  rw [hfun]
  exact hreal

/-- Every level of a nonconstant actual angular projection is null.
The nonconstant/constant split remains explicit; this is an optimizer
ingredient, not an assertion of the still-open inner-circle convex order. -/
theorem actualHarmonic_angular_projection_level_volume_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hnot : ¬ ∃ b : ℝ, ∀ θ : ℝ,
      (c*actualHarmonic F (circleMap 0 r θ)).re=b) (a : ℝ) :
    volume {θ : ℝ | (c*actualHarmonic F (circleMap 0 r θ)).re=a}=0 := by
  exact analyticOn_real_level_volume_zero _
    (actualHarmonic_angular_projection_analytic F hc c hr0 hr1) hnot a

/-- An unconditional actual-F interface for the optimizer construction:
the constant alternative is retained, and no nonconstant premise survives. -/
theorem actualHarmonic_angular_projection_constant_or_level_null
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∃ b : ℝ, ∀ θ : ℝ, (c*actualHarmonic F (circleMap 0 r θ)).re=b) ∨
      ∀ a : ℝ, volume {θ : ℝ | (c*actualHarmonic F (circleMap 0 r θ)).re=a}=0 := by
  classical
  by_cases h : ∃ b : ℝ, ∀ θ : ℝ, (c*actualHarmonic F (circleMap 0 r θ)).re=b
  · exact Or.inl h
  · exact Or.inr (fun a => actualHarmonic_angular_projection_level_volume_zero F hc c hr0 hr1 h a)

end SpringerLean
