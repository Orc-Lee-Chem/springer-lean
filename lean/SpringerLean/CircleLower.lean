import SpringerLean.CircleConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory AddCircle Filter
open scoped Topology

namespace SpringerLean

private instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

private theorem circlePoint_continuous (ρ : ℝ) :
    Continuous (exteriorCirclePoint ρ) := by
  unfold exteriorCirclePoint
  fun_prop

private theorem partialCircle_continuous (F : ℂ → ℂ) (ρ : ℝ) (M : ℕ) :
    Continuous (exteriorDerivativePartialCircle F ρ M) := by
  unfold exteriorDerivativePartialCircle finiteFourierFamily
  fun_prop

theorem actualCircleDerivative_continuous (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) {ρ : ℝ} (hρ : 1 < ρ) :
    Continuous (fun θ : AddCircle (2 * Real.pi) =>
      deriv F (exteriorCirclePoint ρ θ)) := by
  have hderiv : ContinuousOn (deriv F) exteriorDisk :=
    ((hc.1.analyticOnNhd exteriorDisk_isOpen).deriv).continuousOn
  exact hderiv.comp_continuous (circlePoint_continuous ρ)
    (fun θ => exteriorCirclePoint_mem_exteriorDisk hρ θ)

private theorem partialCircle_energy_tendsto (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) {ρ : ℝ} (hρ : 1 < ρ) :
    Tendsto
      (fun M => ∫ θ : AddCircle (2 * Real.pi),
        ‖exteriorDerivativePartialCircle F ρ M θ‖ ^ 2
          ∂(@haarAddCircle (2 * Real.pi) _))
      atTop
      (𝓝 (∫ θ : AddCircle (2 * Real.pi),
        ‖deriv F (exteriorCirclePoint ρ θ)‖ ^ 2
          ∂(@haarAddCircle (2 * Real.pi) _))) := by
  let μ := @haarAddCircle (2 * Real.pi) _
  let p : ℕ → AddCircle (2 * Real.pi) → ℝ :=
    fun M θ => ‖exteriorDerivativePartialCircle F ρ M θ‖ ^ 2
  let q : AddCircle (2 * Real.pi) → ℝ :=
    fun θ => ‖deriv F (exteriorCirclePoint ρ θ)‖ ^ 2
  have hactual := actualCircleDerivative_continuous F hc hρ
  obtain ⟨B, hB⟩ :=
    (isCompact_univ.image hactual).isBounded.exists_norm_le
  have hbound : ∀ θ, ‖deriv F (exteriorCirclePoint ρ θ)‖ ≤ B := by
    intro θ
    exact hB _ (Set.mem_image_of_mem _ (Set.mem_univ θ))
  have huniform := exteriorDerivativePartialCircle_uniform F hc hρ
  have hevent : ∀ᶠ M in atTop, ∀ θ,
      dist (deriv F (exteriorCirclePoint ρ θ))
        (exteriorDerivativePartialCircle F ρ M θ) < 1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp huniform) 1 (by norm_num)]
      with M hM θ
    exact hM θ (Set.mem_univ θ)
  have hboundevent : ∀ᶠ M in atTop, ∀ θ,
      ‖p M θ‖ ≤ (B + 1) ^ 2 := by
    filter_upwards [hevent] with M hM θ
    have hP : ‖exteriorDerivativePartialCircle F ρ M θ‖ ≤ B + 1 := by
      calc
        _ = ‖deriv F (exteriorCirclePoint ρ θ) +
              (exteriorDerivativePartialCircle F ρ M θ -
                deriv F (exteriorCirclePoint ρ θ))‖ := by
          congr 1
          ring
        _ ≤ ‖deriv F (exteriorCirclePoint ρ θ)‖ +
            ‖exteriorDerivativePartialCircle F ρ M θ -
              deriv F (exteriorCirclePoint ρ θ)‖ := by
          exact norm_add_le _ _
        _ ≤ B + 1 := by
          rw [← dist_eq_norm, dist_comm]
          exact add_le_add (hbound θ) (hM θ).le
    have hBpos : 0 ≤ B + 1 := by
      have := hbound θ
      have hq : 0 ≤ ‖deriv F (exteriorCirclePoint ρ θ)‖ := norm_nonneg _
      linarith
    dsimp [p]
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hP _
  have hmeas : ∀ᶠ M in atTop, AEStronglyMeasurable (p M) μ := by
    filter_upwards [] with M
    have hpcont : Continuous (p M) :=
      ((partialCircle_continuous F ρ M).norm.pow 2)
    exact hpcont.aestronglyMeasurable
  have hlim : ∀ᵐ θ ∂μ, Tendsto (fun M => p M θ) atTop (𝓝 (q θ)) := by
    filter_upwards [] with θ
    have ht := huniform.tendsto_at (Set.mem_univ θ)
    dsimp [p, q]
    exact (continuous_norm.pow 2).tendsto _ |>.comp ht
  have hconst : Integrable (fun _ : AddCircle (2 * Real.pi) => (B + 1) ^ 2) μ :=
    integrable_const _
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _ => (B + 1) ^ 2) hmeas _ hconst hlim
  filter_upwards [hboundevent] with M hM
  filter_upwards [] with θ
  exact hM θ

/-- A fixed finite collection of actual derivative modes contributes at most
the full circle energy. This is the finite Bessel lower bound needed by the
annulus argument. -/
theorem exteriorDerivativeCircle_finite_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ) :
    1 + ∑ j ∈ Finset.Icc 1 N,
      (j : ℝ) ^ 2 * ‖exteriorForwardCoeff F j‖ ^ 2 *
        (ρ⁻¹) ^ (2 * j + 2) ≤
      ∫ θ : AddCircle (2 * Real.pi),
        ‖deriv F (exteriorCirclePoint ρ θ)‖ ^ 2
          ∂(@haarAddCircle (2 * Real.pi) _) := by
  have hlimit := partialCircle_energy_tendsto F hc hρ
  apply ge_of_tendsto hlimit
  filter_upwards [eventually_ge_atTop N] with M hM
  rw [exteriorDerivativePartialCircle_energy_formula F (by linarith : 0 < ρ) M]
  gcongr

/-- The paper's normalized angular integral version of the finite Bessel
lower bound, with the actual derivative of the same `F`. -/
theorem exteriorDerivativeCircle_interval_finite_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ) :
    1 + ∑ j ∈ Finset.Icc 1 N,
      (j : ℝ) ^ 2 * ‖exteriorForwardCoeff F j‖ ^ 2 *
        (ρ⁻¹) ^ (2 * j + 2) ≤
      (1 / (2 * Real.pi)) *
        ∫ θ in -Real.pi..Real.pi,
          ‖deriv F (exteriorCirclePoint ρ
            (θ : AddCircle (2 * Real.pi)))‖ ^ 2 := by
  have hinterval :
      (∫ θ in -Real.pi..Real.pi,
        ‖deriv F (exteriorCirclePoint ρ
          (θ : AddCircle (2 * Real.pi)))‖ ^ 2) =
      ∫ θ : AddCircle (2 * Real.pi),
        ‖deriv F (exteriorCirclePoint ρ θ)‖ ^ 2 := by
    simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using
      (AddCircle.intervalIntegral_preimage (2 * Real.pi) (-Real.pi)
        (fun θ : AddCircle (2 * Real.pi) =>
          ‖deriv F (exteriorCirclePoint ρ θ)‖ ^ 2))
  have hhaar :
      (∫ θ : AddCircle (2 * Real.pi),
        ‖deriv F (exteriorCirclePoint ρ θ)‖ ^ 2
        ∂(@haarAddCircle (2 * Real.pi) _)) =
      (2 * Real.pi)⁻¹ *
        (∫ θ : AddCircle (2 * Real.pi),
          ‖deriv F (exteriorCirclePoint ρ θ)‖ ^ 2) := by
    simpa only [smul_eq_mul] using
      (AddCircle.integral_haarAddCircle (T := 2 * Real.pi)
        (f := fun θ : AddCircle (2 * Real.pi) =>
          ‖deriv F (exteriorCirclePoint ρ θ)‖ ^ 2))
  convert exteriorDerivativeCircle_finite_energy_le F hc hρ N using 1
  rw [hinterval, hhaar]
  ring

end SpringerLean
