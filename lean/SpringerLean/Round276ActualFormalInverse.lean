import SpringerLean.Round270ActualTaylorComposition
import SpringerLean.Round272ActualInverseLagrange

open scoped Topology

namespace SpringerLean
open PowerSeries

theorem exteriorForwardGerm_comp_actualReciprocal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    (fun t => exteriorForwardGerm F (schoberActualReciprocalGerm F t))
      =ᶠ[𝓝 (0 : ℂ)] exteriorInverseGerm F := by
  obtain ⟨V, hV0, hVa, hVd, hfunc⟩ := exterior_inverse_functional_germs F hc
  have hD : ContinuousAt
      (fun t : ℂ => 1 - t * exteriorInverseGerm F t) 0 := by
    have hB := (exteriorInverseGerm_analyticAt F hc).continuousAt
    fun_prop
  have hD0 : (1 - (0 : ℂ) * exteriorInverseGerm F 0) ≠ 0 := by norm_num
  filter_upwards [hfunc, hD.eventually_ne hD0] with t ht hDt
  have heq : schoberActualReciprocalGerm F t = V t := by
    apply (div_eq_iff hDt).2
    have hv : V t = t * (1 + V t * exteriorInverseGerm F t) := by
      simpa only [exteriorPhi, ← ht.2] using ht.1
    linear_combination -hv
  rw [heq, ← ht.2]

theorem exteriorForwardGerm_actualTaylorSeries (F : ℂ → ℂ) :
    actualTaylorSeries (exteriorForwardGerm F) = exteriorFormalForward F := by
  ext n
  rfl

/-- The forward coefficients and inverse coefficients are independently
read from the same actual map; their formal substitution relation is
proved using the analytic inverse, not included as a class assumption. -/
theorem schoberActual_forward_subst_inverse
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    (exteriorFormalForward F).subst
      (schoberReciprocalSeries (schoberActualInverseSeries F)) =
        schoberActualInverseSeries F := by
  have hH := schoberActualReciprocalGerm_analyticAt F hc
  have hH0 : schoberActualReciprocalGerm F 0 = 0 := by
    simp [schoberActualReciprocalGerm]
  rw [← exteriorForwardGerm_actualTaylorSeries,
    ← schoberActualReciprocalGerm_taylorSeries F hc,
    ← actualTaylorSeries_comp_zero _ _ hc.2.2 hH hH0]
  ext n
  simp only [actualTaylorSeries_coeff, schoberActualInverseSeries]
  exact actualTaylorCoeff_congr (exteriorForwardGerm_comp_actualReciprocal F hc) n

theorem schoberActual_reciprocal_times_denominator (F : ℂ → ℂ) :
    schoberReciprocalSeries (schoberActualInverseSeries F) *
      (1 - PowerSeries.X * schoberActualInverseSeries F) = PowerSeries.X := by
  have hD0 : PowerSeries.constantCoeff
      (1 - PowerSeries.X * schoberActualInverseSeries F) ≠ 0 := by simp
  change (PowerSeries.X * (1 - PowerSeries.X * schoberActualInverseSeries F)⁻¹) *
    (1 - PowerSeries.X * schoberActualInverseSeries F) = PowerSeries.X
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hD0, mul_one]

end SpringerLean
