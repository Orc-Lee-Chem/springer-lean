import SpringerLean.Round1990OddStarOuterCircleRotation

open MeasureTheory Filter Set
open scoped Topology

namespace SpringerLean

theorem oddStarPerturbation_measurable (m : ℕ) (t : ℝ) :
    Measurable (oddStarPerturbation m t) := by
  unfold oddStarPerturbation oddStarSeedRootReciprocal
  fun_prop

/-- The actual smooth outer-circle law is the image of the normalized
angular probability under the same actual exterior values. -/
theorem oddStarOuterCircleProbability_eq_angular_map
    (m : ℕ) (t s : ℝ) :
    oddStarOuterCircleProbability m t s =
      oddStarAngularProbability.map
        (fun θ : ℝ => oddStarPerturbation m t
          ((s⁻¹ : ℂ) * Complex.polarCoord.symm (1, θ))) := by
  have hpolar : Measurable
      (fun θ : ℝ => Complex.polarCoord.symm (1, θ)) := by
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  have hf : Measurable (fun u : ℂ =>
      oddStarPerturbation m t ((s⁻¹ : ℂ) * u)) :=
    (oddStarPerturbation_measurable m t).comp (by fun_prop)
  unfold oddStarOuterCircleProbability oddStarUnitCircleProbability
  exact Measure.map_map hf hpolar

/-- Weak convergence of actual outer-circle image laws to the actual
almost-everywhere radial boundary law, tested on any bounded continuous
real function. -/
theorem oddStarOuterCircleProbability_integral_tendsto_actual
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    (φ : BoundedContinuousFunction ℂ ℝ) :
    Tendsto
      (fun s : ℝ => ∫ u, φ u ∂oddStarOuterCircleProbability m t s)
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ u, φ u ∂oddStarActualBoundaryProbability m t)) := by
  let F : ℂ → ℂ := oddStarPerturbation m t
  let μ : Measure ℝ := oddStarAngularProbability
  have hF : Measurable F := oddStarPerturbation_measurable m t
  have hpolar : Measurable
      (fun θ : ℝ => Complex.polarCoord.symm (1, θ)) := by
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  have hmeas : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      AEStronglyMeasurable
        (fun θ : ℝ => φ (F ((s⁻¹ : ℂ) *
          Complex.polarCoord.symm (1, θ)))) μ := by
    apply Filter.Eventually.of_forall
    intro s
    exact (φ.continuous.measurable.comp
      (hF.comp ((by fun_prop : Measurable (fun θ : ℝ =>
        (s⁻¹ : ℂ) * Complex.polarCoord.symm (1, θ)))))).aestronglyMeasurable
  have hbound : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      ∀ᵐ θ : ℝ ∂μ,
        ‖φ (F ((s⁻¹ : ℂ) * Complex.polarCoord.symm (1, θ)))‖ ≤ ‖φ‖ := by
    apply Filter.Eventually.of_forall
    intro s
    filter_upwards with θ
    exact BoundedContinuousFunction.norm_coe_le_norm φ _
  have hμac : μ ≪ oddStarAngularMeasure := by
    dsimp [μ, oddStarAngularProbability]
    exact Measure.smul_absolutelyContinuous
  have htrace : ∀ᵐ θ : ℝ ∂μ,
      Tendsto (fun s : ℝ => F (Complex.polarCoord.symm (s⁻¹, θ)))
        (𝓝[<] (1 : ℝ))
        (𝓝 (actualExteriorRadialTrace F θ)) :=
    (actualExteriorRadialTrace_ae_tendsto F
      (oddStarPerturbation_centeredExteriorUnivalent m hm t ht)).filter_mono
        (Measure.ae_mono' hμac)
  have hpoint : ∀ᵐ θ : ℝ ∂μ,
      Tendsto (fun s : ℝ => φ (F ((s⁻¹ : ℂ) *
          Complex.polarCoord.symm (1, θ))))
        (𝓝[<] (1 : ℝ))
        (𝓝 (φ (actualExteriorRadialTrace F θ))) := by
    filter_upwards [htrace] with θ hθ
    have harg (s : ℝ) :
        (s⁻¹ : ℂ) * Complex.polarCoord.symm (1, θ) =
          Complex.polarCoord.symm (s⁻¹, θ) := by
      simpa only [Complex.ofReal_inv] using
        (polar_radius_eq_mul_unit (s⁻¹) θ).symm
    simpa only [harg, Function.comp_def] using
      φ.continuous.continuousAt.tendsto.comp hθ
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (fun _ : ℝ => ‖φ‖) hmeas hbound
      (integrable_const _) hpoint
  have hleft (s : ℝ) :
      (∫ u, φ u ∂oddStarOuterCircleProbability m t s) =
        ∫ θ, φ (F ((s⁻¹ : ℂ) *
          Complex.polarCoord.symm (1, θ))) ∂μ := by
    rw [oddStarOuterCircleProbability_eq_angular_map]
    exact integral_map
      ((hF.comp (by fun_prop : Measurable (fun θ : ℝ =>
        (s⁻¹ : ℂ) * Complex.polarCoord.symm (1, θ)))).aemeasurable)
      φ.continuous.aestronglyMeasurable
  have htraceMeas : AEMeasurable
      (actualExteriorRadialTrace F) μ := by
    exact ((actualExteriorRadialTrace_aestronglyMeasurable F
      (oddStarPerturbation_centeredExteriorUnivalent m hm t ht)).aemeasurable).mono_ac
        hμac
  have hright :
      (∫ u, φ u ∂oddStarActualBoundaryProbability m t) =
        ∫ θ, φ (actualExteriorRadialTrace F θ) ∂μ := by
    unfold oddStarActualBoundaryProbability
    exact integral_map htraceMeas φ.continuous.aestronglyMeasurable
  simpa only [← hleft, ← hright] using hlim

end SpringerLean

#print axioms SpringerLean.oddStarPerturbation_measurable
#print axioms SpringerLean.oddStarOuterCircleProbability_integral_tendsto_actual
