import SpringerLean.Round1333ActualExteriorCircleParseval
import Mathlib.Analysis.Normed.Group.Tannery

open Filter
open scoped Topology

namespace SpringerLean

/-- Dominated convergence for the actual forward-coefficient square
series as an inner radius tends to one.  It requires no radial boundary
trace, so that trace remains a separate analytic obligation. -/
theorem exteriorForwardCoeff_sq_tsum_tendsto_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {𝓕 : Filter ℝ}
    (hnear : ∀ᶠ r in 𝓕, 0 ≤ r ∧ r ≤ 1)
    (hr : Tendsto (fun r : ℝ => r) 𝓕 (𝓝 1)) :
    Tendsto
      (fun r : ℝ => ∑' j : ℕ,
        ‖exteriorForwardCoeff F j‖ ^ 2 * r ^ (2 * j))
      𝓕
      (𝓝 (∑' j : ℕ, ‖exteriorForwardCoeff F j‖ ^ 2)) := by
  let b : ℕ → ℝ := fun j => ‖exteriorForwardCoeff F j‖ ^ 2
  have hsum : Summable b := exteriorForwardCoeff_sq_summable F hc
  have hterm (j : ℕ) :
      Tendsto (fun r : ℝ => b j * r ^ (2 * j)) 𝓕 (𝓝 (b j)) := by
    have hpow : Tendsto (fun r : ℝ => r ^ (2 * j)) 𝓕 (𝓝 (1 : ℝ)) := by
      have hcont : ContinuousAt (fun r : ℝ => r ^ (2 * j)) 1 := by fun_prop
      simpa only [Function.comp_def, one_pow] using hcont.tendsto.comp hr
    simpa using tendsto_const_nhds.mul hpow
  have hbound : ∀ᶠ r in 𝓕, ∀ j : ℕ,
      ‖b j * r ^ (2 * j)‖ ≤ b j := by
    filter_upwards [hnear] with r hrange j
    have hp : 0 ≤ r ^ (2 * j) := pow_nonneg hrange.1 _
    have hp1 : r ^ (2 * j) ≤ 1 := pow_le_one₀ hrange.1 hrange.2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hp)]
    exact mul_le_of_le_one_right (sq_nonneg _) hp1
  exact tendsto_tsum_of_dominated_convergence hsum hterm hbound

/-- The actual exterior-circle second moments converge to the full
coefficient-square expression when their reciprocal radii tend to one
from below.  This still does not identify an a.e. radial boundary trace. -/
theorem exterior_actual_circle_two_energy_tendsto_boundary_coeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {𝓕 : Filter ℝ}
    (hnear : ∀ᶠ r in 𝓕, 0 < r ∧ r < 1)
    (hr : Tendsto (fun r : ℝ => r) 𝓕 (𝓝 1)) :
    Tendsto
      (fun r : ℝ => Real.circleAverage
        (fun z : ℂ => ‖F z‖ ^ 2) 0 r⁻¹)
      𝓕
      (𝓝 (1 + ∑' j : ℕ, ‖exteriorForwardCoeff F j‖ ^ 2)) := by
  have hlead : Tendsto (fun r : ℝ => (r⁻¹) ^ 2) 𝓕 (𝓝 (1 : ℝ)) := by
    have hcont : ContinuousAt (fun r : ℝ => (r⁻¹) ^ 2) 1 :=
      (continuousAt_id.inv₀ (by norm_num)).pow 2
    simpa only [Function.comp_def, inv_one, one_pow] using hcont.tendsto.comp hr
  have hseries := exteriorForwardCoeff_sq_tsum_tendsto_one F hc
    (hnear.mono (fun r h => ⟨h.1.le, h.2.le⟩)) hr
  have hsum := hlead.add hseries
  apply hsum.congr'
  filter_upwards [hnear] with r hrange
  exact (exterior_actual_circle_two_energy_eq F hc hrange.1 hrange.2).symm

end SpringerLean

#print axioms SpringerLean.exteriorForwardCoeff_sq_tsum_tendsto_one
#print axioms SpringerLean.exterior_actual_circle_two_energy_tendsto_boundary_coeff
