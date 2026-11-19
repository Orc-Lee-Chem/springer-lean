import SpringerLean.Round1506PoissonThresholdInverse
import SpringerLean.Round38CenteredWeighted

open MeasureTheory Set
open scoped ComplexConjugate

namespace SpringerLean

/-- Two angular sets with the same intersection with the normalized
one-turn domain have the same set integral under its restricted measure. -/
theorem oneTurn_setIntegral_congr_inter
    (E H : Set ℝ) (hE : MeasurableSet E) (hH : MeasurableSet H)
    (hEq : (Ioc (0:ℝ) (2*Real.pi)) ∩ E =
      (Ioc (0:ℝ) (2*Real.pi)) ∩ H)
    (f : ℝ → ℝ) :
    (∫ θ in E, f θ ∂(volume.restrict (Ioc (0:ℝ) (2*Real.pi)))) =
      (∫ θ in H, f θ ∂(volume.restrict (Ioc (0:ℝ) (2*Real.pi)))) := by
  simp only [Measure.restrict_restrict hE,Measure.restrict_restrict hH]
  rw [inter_comm E (Ioc (0:ℝ) (2*Real.pi)),
    inter_comm H (Ioc (0:ℝ) (2*Real.pi)),hEq]

/-- The regularized actual projection has raw full-turn mean zero. -/
theorem regularExterior_projected_raw_turn_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ξ : ℂ) :
    (∫ θ : ℝ,
      (conj ξ*rescaleExterior s F (circleMap 0 1 θ)).re
        ∂(volume.restrict (Ioc (0:ℝ) (2*Real.pi)))) = 0 := by
  have hmean := rescaleExterior_projected_boundary_circleAverage_zero
    F hc hs0 hs1 ξ
  rw [circleAverage_eq_restrictedAngularIntegral] at hmean
  have hne : (2*Real.pi)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  exact (mul_eq_zero.mp hmean).resolve_left hne

end SpringerLean

#print axioms SpringerLean.oneTurn_setIntegral_congr_inter
#print axioms SpringerLean.regularExterior_projected_raw_turn_zero
