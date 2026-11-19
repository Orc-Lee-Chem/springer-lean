import SpringerLean.Round14CircleParseval
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory AddCircle Filter
open scoped Topology

namespace SpringerLean

private instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

/-- Uniform convergence of continuous complex functions on the compact
angle circle passes to the normalized square-modulus integrals. -/
theorem circle_energy_tendsto_of_uniform
    (p : ℕ → AddCircle (2 * Real.pi) → ℂ)
    (q : AddCircle (2 * Real.pi) → ℂ)
    (hp : ∀ M, Continuous (p M)) (hq : Continuous q)
    (hu : TendstoUniformlyOn p q atTop Set.univ) :
    Tendsto
      (fun M => ∫ θ : AddCircle (2 * Real.pi), ‖p M θ‖ ^ 2
        ∂haarAddCircle)
      atTop
      (nhds (∫ θ : AddCircle (2 * Real.pi), ‖q θ‖ ^ 2
        ∂haarAddCircle)) := by
  let μ := @haarAddCircle (2 * Real.pi) _
  let p2 : ℕ → AddCircle (2 * Real.pi) → ℝ := fun M θ => ‖p M θ‖ ^ 2
  let q2 : AddCircle (2 * Real.pi) → ℝ := fun θ => ‖q θ‖ ^ 2
  obtain ⟨B, hB⟩ :=
    (isCompact_univ.image hq).isBounded.exists_norm_le
  have hbound : ∀ θ, ‖q θ‖ ≤ B := by
    intro θ
    exact hB _ (Set.mem_image_of_mem _ (Set.mem_univ θ))
  have hevent : ∀ᶠ M in atTop, ∀ θ,
      dist (p M θ) (q θ) < 1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) 1 (by norm_num)]
      with M hM θ
    simpa only [dist_comm] using hM θ (Set.mem_univ θ)
  have hboundevent : ∀ᶠ M in atTop, ∀ θ,
      ‖p2 M θ‖ ≤ (B + 1) ^ 2 := by
    filter_upwards [hevent] with M hM θ
    have hP : ‖p M θ‖ ≤ B + 1 := by
      calc
        ‖p M θ‖ = ‖q θ + (p M θ - q θ)‖ := by congr 1; ring
        _ ≤ ‖q θ‖ + ‖p M θ - q θ‖ := norm_add_le _ _
        _ ≤ B + 1 := by
          rw [← dist_eq_norm]
          exact add_le_add (hbound θ) (hM θ).le
    have hBpos : 0 ≤ B + 1 := by
      have := hbound θ
      have hqnonneg : 0 ≤ ‖q θ‖ := norm_nonneg _
      linarith
    dsimp [p2]
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hP _
  have hmeas : ∀ᶠ M in atTop, AEStronglyMeasurable (p2 M) μ := by
    filter_upwards [] with M
    exact ((hp M).norm.pow 2).aestronglyMeasurable
  have hlim : ∀ᵐ θ ∂μ, Tendsto (fun M => p2 M θ) atTop (nhds (q2 θ)) := by
    filter_upwards [] with θ
    have ht := hu.tendsto_at (Set.mem_univ θ)
    exact (continuous_norm.pow 2).tendsto _ |>.comp ht
  have hconst : Integrable (fun _ : AddCircle (2 * Real.pi) => (B + 1) ^ 2) μ :=
    integrable_const _
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _ => (B + 1) ^ 2) hmeas _ hconst hlim
  filter_upwards [hboundevent] with M hM
  filter_upwards [] with θ
  exact hM θ

end SpringerLean