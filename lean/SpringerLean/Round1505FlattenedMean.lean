import SpringerLean.Round1504PoissonLevelParameter

open MeasureTheory Set

namespace SpringerLean

/-- The centered plateau has the same full-turn mean as `2 cos`, namely
zero. This supplies the full-superlevel endpoint of the layer cake. -/
theorem cappedAngularCosine_full_turn_zero
    {h R : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hbalance : 2*h*R=4*Real.sin h) :
    (∫ θ in Ioc (0:ℝ) (2*Real.pi),
      cappedAngularCosine R h θ) = 0 := by
  classical
  let A : Set ℝ := centeredAngularArc h
  let I : Set ℝ := Ioc (0:ℝ) (2*Real.pi)
  let μ : Measure ℝ := volume.restrict I
  let g : ℝ → ℝ := fun θ => 2*Real.cos θ
  have hAmeas : MeasurableSet A := measurableSet_Ioc.union measurableSet_Icc
  have hsub : A ⊆ I := by
    intro θ hθ
    rcases hθ with hl|hr
    · exact ⟨hl.1,by linarith [hl.2]⟩
    · exact ⟨by linarith [hr.1],hr.2⟩
  haveI : IsFiniteMeasure μ := Real.isFiniteMeasure_restrict_Ioc 0 (2*Real.pi)
  have hgInt : Integrable g μ := by
    apply Integrable.mono' (g := fun _ : ℝ => (2:ℝ)) (integrable_const 2)
      (by fun_prop : Continuous g).measurable.aestronglyMeasurable
    filter_upwards [] with θ
    dsimp [g]
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),mul_one]
      using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (by norm_num : (0:ℝ)≤2)
  have hconstInt : Integrable (fun _ : ℝ => R) μ := integrable_const R
  have hpiece :
      (∫ θ, cappedAngularCosine R h θ ∂μ) =
      (∫ θ in A, R ∂μ) + (∫ θ in Aᶜ, g θ ∂μ) := by
    change (∫ θ, A.piecewise (fun _ => R) g θ ∂μ) = _
    exact integral_piecewise hAmeas hconstInt.integrableOn hgInt.integrableOn
  have hconst : (∫ θ in A, R ∂μ) = 2*h*R := by
    have hr : (∫ θ in A, R ∂μ) = ∫ θ in A, R := by
      dsimp [μ]
      rw [Measure.restrict_restrict_of_subset hsub]
    rw [hr,setIntegral_const,Measure.real_def,
      centeredAngularArc_volume h hh0.le hhpi,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*h)]
    simp only [smul_eq_mul]
  have hcosA : (∫ θ in A, g θ ∂μ) = 4*Real.sin h := by
    have hr : (∫ θ in A, g θ ∂μ) = ∫ θ in A, g θ := by
      dsimp [μ]
      rw [Measure.restrict_restrict_of_subset hsub]
    rw [hr]
    exact centeredAngularArc_comparator_integral h hh0.le hhpi
  have hcosI : (∫ θ, g θ ∂μ) = 0 := by
    change (∫ θ in Ioc (0:ℝ) (2*Real.pi), 2*Real.cos θ) = 0
    rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi),
      intervalIntegral.integral_const_mul, integral_cos]
    simp [Real.sin_two_pi]
  have hsplit := integral_add_compl (μ := μ) hAmeas hgInt
  have hmodel : (∫ θ, cappedAngularCosine R h θ ∂μ) =
      ∫ θ, g θ ∂μ := by
    rw [hpiece,←hsplit]
    linarith
  exact hmodel.trans hcosI

end SpringerLean

#print axioms SpringerLean.cappedAngularCosine_full_turn_zero
