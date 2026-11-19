import SpringerLean.Round17LogRadial
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set

namespace SpringerLean

/-- On any bounded interval of strictly positive scales, the Cauchy
parameter kernel is jointly integrable against scale × vertical area. -/
theorem verticalCauchyKernel_integrable_prod_Ioc
    {l u : ℝ} (hl : 0 ≤ l) :
    Integrable (fun p : ℝ × ℝ => p.1 / (p.1 ^ 2 + p.2 ^ 2))
      ((volume.restrict (Ioc l u)).prod volume) := by
  let μ : Measure ℝ := volume.restrict (Ioc l u)
  haveI : IsFiniteMeasure μ := Real.isFiniteMeasure_restrict_Ioc l u
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => p.1 / (p.1 ^ 2 + p.2 ^ 2)) (μ.prod volume) := by
    have h : Measurable (fun p : ℝ × ℝ => p.1 / (p.1 ^ 2 + p.2 ^ 2)) := by
      measurability
    exact h.aestronglyMeasurable
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with lam hlam
    exact verticalCauchyKernel_integrable (lt_of_le_of_lt hl hlam.1)
  · have heq : (fun lam : ℝ => ∫ t : ℝ, ‖lam / (lam ^ 2 + t ^ 2)‖) =ᵐ[μ]
        fun _ => Real.pi := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with lam hlam
      have hpos : 0 < lam := lt_of_le_of_lt hl hlam.1
      have hnonneg (t : ℝ) : 0 ≤ lam / (lam ^ 2 + t ^ 2) := by
        positivity
      have hpoint (t : ℝ) : ‖lam / (lam ^ 2 + t ^ 2)‖ =
          lam / (lam ^ 2 + t ^ 2) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t)]
      simp_rw [hpoint]
      exact verticalCauchyKernel_integral hpos
    exact (integrable_const (μ := μ) (c := Real.pi)).congr heq.symm

end SpringerLean
