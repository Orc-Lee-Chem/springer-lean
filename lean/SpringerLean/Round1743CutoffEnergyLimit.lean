import SpringerLean.Round1740ActualEnergyIntegrationReduction
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter MeasureTheory
open scoped Topology

namespace SpringerLean

/-- Bounded cutoffs converging to one preserve the integral of every
L1 density. This is used only for the potential and energy densities,
so no integrability assumption on the unweighted divergence enters. -/
theorem tendsto_integral_bounded_cutoff
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (η : ℕ → α → ℝ) (g : α → ℝ)
    (hg : Integrable g μ)
    (hηmeas : ∀ j, AEStronglyMeasurable (η j) μ)
    (hη : ∀ j, ∀ᵐ z ∂μ, 0 ≤ η j z ∧ η j z ≤ 1)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun j => η j z) atTop (𝓝 1)) :
    Tendsto (fun j => ∫ z, η j z * g z ∂μ) atTop
      (𝓝 (∫ z, g z ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun z => ‖g z‖)
  · intro j
    exact (hηmeas j).mul hg.aestronglyMeasurable
  · exact hg.norm
  · intro j
    filter_upwards [hη j] with z hz
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hz.1]
    exact (mul_le_mul_of_nonneg_right hz.2 (norm_nonneg _)).trans_eq
      (one_mul _)
  · filter_upwards [hlim] with z hz
    simpa using hz.mul_const (g z)

/-- The energy limit needs only the weighted divergence identities.
It does not assume the full divergence is integrable. The boundary
term is recorded with the integration-by-parts sign. -/
theorem integral_energy_le_of_cutoff_flux_balance
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (e f q : α → ℝ) (b : ℝ)
    (η : ℕ → α → ℝ) (boundary : ℕ → ℝ)
    (he : Integrable e μ) (hf : Integrable f μ)
    (hηmeas : ∀ j, AEStronglyMeasurable (η j) μ)
    (hη : ∀ j, ∀ᵐ z ∂μ, 0 ≤ η j z ∧ η j z ≤ 1)
    (hηlim : ∀ᵐ z ∂μ, Tendsto (fun j => η j z) atTop (𝓝 1))
    (hpoint : ∀ᵐ z ∂μ, e z + b*q z ≤ f z)
    (hweighted : ∀ j, Integrable (fun z => η j z * q z) μ)
    (hbalance : ∀ j, (∫ z, η j z * q z ∂μ) = -boundary j)
    (hboundary : Tendsto boundary atTop (𝓝 0)) :
    (∫ z, e z ∂μ) ≤ ∫ z, f z ∂μ := by
  have hcutInt (j : ℕ) (g : α → ℝ) (hg : Integrable g μ) :
      Integrable (fun z => η j z * g z) μ := by
    apply hg.bdd_mul (hηmeas j)
    filter_upwards [hη j] with z hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg hz.1] using hz.2
  have hle (j : ℕ) :
      (∫ z, η j z * e z ∂μ) - b*boundary j ≤
        ∫ z, η j z * f z ∂μ := by
    have hp : ∀ᵐ z ∂μ,
        η j z * e z + b*(η j z*q z) ≤ η j z*f z := by
      filter_upwards [hpoint, hη j] with z hp hz
      nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hp)]
    have hmain := integral_mono_ae
      ((hcutInt j e he).add ((hweighted j).const_mul b))
      (hcutInt j f hf) hp
    rw [integral_add' (hcutInt j e he) ((hweighted j).const_mul b),
      integral_const_mul, hbalance j] at hmain
    linarith
  have heLim := tendsto_integral_bounded_cutoff μ η e he hηmeas hη hηlim
  have hfLim := tendsto_integral_bounded_cutoff μ η f hf hηmeas hη hηlim
  have hleft : Tendsto
      (fun j => (∫ z, η j z*e z ∂μ) - b*boundary j)
      atTop (𝓝 ((∫ z, e z ∂μ)-b*0)) :=
    heLim.sub (hboundary.const_mul b)
  have hfinal := le_of_tendsto_of_tendsto hleft hfLim
    (Filter.Eventually.of_forall hle)
  simpa using hfinal

end SpringerLean

#print axioms SpringerLean.integral_energy_le_of_cutoff_flux_balance
