import SpringerLean.Round257AllOrderActualFaber
import SpringerLean.Round75DiagonalRows

open scoped Topology

namespace SpringerLean
open PowerSeries

/-- The reciprocal coordinate read from the actual inverse is the same
local inverse which was constructed from the forward map. -/
theorem schoberActualReciprocalGerm_eq_localInverse
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∃ V : ℂ → ℂ,
      V 0 = 0 ∧ AnalyticAt ℂ V 0 ∧ deriv V 0 = 1 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), V t = t * exteriorPhi F (V t)) ∧
      schoberActualReciprocalGerm F =ᶠ[𝓝 (0 : ℂ)] V := by
  obtain ⟨V, hV0, hVa, hVd, hfunc⟩ := exterior_inverse_functional_germs F hc
  have hD : ContinuousAt
      (fun t : ℂ => 1 - t * exteriorInverseGerm F t) 0 := by
    have hB := (exteriorInverseGerm_analyticAt F hc).continuousAt
    fun_prop
  have hD0 : (1 - (0 : ℂ) * exteriorInverseGerm F 0) ≠ 0 := by norm_num
  refine ⟨V, hV0, hVa, hVd, hfunc.mono (fun t ht => ht.1), ?_⟩
  filter_upwards [hfunc, hD.eventually_ne hD0] with t ht hDt
  apply (div_eq_iff hDt).2
  have hv : V t = t * (1 + V t * exteriorInverseGerm F t) := by
    simpa only [exteriorPhi, ← ht.2] using ht.1
  linear_combination -hv

/-- Exact all-order Lagrange formula for the derivative-defined coefficients
of the actual reciprocal inverse. This fixes both the inverse branch and
the indices used by the Schober/Gram comparison diagonal. -/
theorem schoberActualA_lagrange
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (n j : ℕ)
    (hjn : j ≤ n) :
    ((n + 1 : ℕ) : ℂ) * schoberActualA F (n + 1) (j + 1) =
      ((j + 1 : ℕ) : ℂ) *
        PowerSeries.coeff (n - j)
          (formalExteriorPhi (exteriorFormalForward F) ^ (n + 1)) := by
  obtain ⟨V, hV0, hVa, hVd, hfunc, hEq⟩ :=
    schoberActualReciprocalGerm_eq_localInverse F hc
  have hA : schoberActualA F (n + 1) (j + 1) =
      actualTaylorCoeff (fun t => V t ^ (j + 1)) (n + 1) := by
    rw [schoberActualA_eq_actualTaylorCoeff F hc]
    exact actualTaylorCoeff_congr
      (hEq.mono (fun t ht => congrArg (fun w : ℂ => w ^ (j + 1)) ht)) (n + 1)
  rw [hA]
  have hL := analytic_lagrange_coefficient (exteriorPhi F) V
    (exteriorPhi_analyticAt F hc.2.2) (exteriorPhi_zero F)
    hVa hV0 hVd hfunc n (fun u : ℂ => u ^ (j + 1)) (by fun_prop)
  rw [show ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 by push_cast; rfl, hL]
  have hDer (u : ℂ) : deriv (fun u : ℂ => u ^ (j + 1)) u =
      ((j + 1 : ℕ) : ℂ) * u ^ j := by
    simpa only [Nat.add_sub_cancel] using (hasDerivAt_pow (j + 1) u).deriv
  simp_rw [hDer]
  have hφ := exteriorPhi_analyticAt F hc.2.2
  have hS : actualTaylorSeries
      (fun u => (((j + 1 : ℕ) : ℂ) * u ^ j) * exteriorPhi F u ^ (n + 1)) =
      PowerSeries.C (((j + 1 : ℕ) : ℂ)) * PowerSeries.X ^ j *
        formalExteriorPhi (exteriorFormalForward F) ^ (n + 1) := by
    rw [actualTaylorSeries_mul _ _ (by fun_prop) (by fun_prop),
      actualTaylorSeries_const_mul, actualTaylorSeries_monomial,
      exteriorPhi_pow_actualTaylorSeries F hc]
  rw [← actualTaylorSeries_coeff, hS, mul_assoc,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  simp only [if_pos hjn]

end SpringerLean
