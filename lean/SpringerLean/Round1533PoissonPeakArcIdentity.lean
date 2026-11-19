import SpringerLean.Round1532CenteredArcSymmetry

open MeasureTheory Set

namespace SpringerLean
set_option maxHeartbeats 640000

/-- Exact normalized peak defect: the full-turn flattened model differs
from the uncut first Poisson mode only on the two centered cap arcs. -/
theorem flattenedCosinePoisson_peak_defect_half_arc
    {h r : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hr0 : 0 < r) (hr1 : r < 1) :
    2*r-flattenedCosinePoissonAtReal h r =
      Real.pi⁻¹ *
        (∫ θ in Ioc (0:ℝ) h,
          ((2-2*Real.sin h/h)-2*(1-Real.cos θ)) *
            poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)) := by
  classical
  let A : Set ℝ := centeredAngularArc h
  let I : Set ℝ := Ioc (0:ℝ) (2*Real.pi)
  let μ : Measure ℝ := volume.restrict I
  let P : ℝ → ℝ := fun θ => poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)
  let g : ℝ → ℝ := fun θ => 2*Real.cos θ*P θ
  let c : ℝ → ℝ := fun θ => (2*Real.sin h/h)*P θ
  let z : ℝ → ℝ := fun θ =>
    ((2-2*Real.sin h/h)-2*(1-Real.cos θ))*P θ
  have hAmeas : MeasurableSet A := measurableSet_Ioc.union measurableSet_Icc
  have hsub : A ⊆ I := by
    intro θ hθ
    rcases hθ with hl|hr
    · exact ⟨hl.1,by linarith [hl.2]⟩
    · exact ⟨by linarith [hr.1,Real.pi_pos],hr.2⟩
  have hPc : Continuous P := centeredPoisson_weight_continuous hr0 hr1
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hcc : Continuous c := hPc.const_mul _
  have hzc : Continuous z := by dsimp [z]; fun_prop
  have hgi : Integrable g μ := by
    change IntegrableOn g I
    exact (hgc.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hci : Integrable c μ := by
    change IntegrableOn c I
    exact (hcc.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hpiece :
      (∫ θ, cappedAngularCosine (2*Real.sin h/h) h θ * P θ ∂μ) =
      (∫ θ in A, c θ ∂μ)+(∫ θ in Aᶜ, g θ ∂μ) := by
    have hfun : (fun θ => cappedAngularCosine (2*Real.sin h/h) h θ * P θ) =
        A.piecewise c g := by
      funext θ
      by_cases hθ : θ ∈ A
      · simp [cappedAngularCosine,Set.piecewise,hθ,A,c]
      · simp [cappedAngularCosine,Set.piecewise,hθ,A,g]
    rw [hfun]
    exact integral_piecewise hAmeas hci.integrableOn hgi.integrableOn
  have hsplit := integral_add_compl (μ:=μ) hAmeas hgi
  have hAeq :
      (∫ θ in A, g θ-c θ ∂μ) =
        2*(∫ θ in Ioc (0:ℝ) h, z θ) := by
    have hpoint : ∀ θ, g θ-c θ=z θ := by
      intro θ; dsimp [g,c,z]; ring
    simp_rw [hpoint]
    change (∫ θ : ℝ, z θ ∂(μ.restrict A)) = _
    dsimp [μ]
    rw [Measure.restrict_restrict_of_subset hsub]
    have hsym (θ : ℝ) : z (2*Real.pi-θ)=z θ := by
      dsimp [z,P]
      rw [Real.cos_two_pi_sub,
        poissonKernel_centered_cosine_formula hr0.le hr1,
        poissonKernel_centered_cosine_formula hr0.le hr1,
        Real.cos_two_pi_sub]
    exact centeredAngularArc_integral_symmetric z hzc hsym hh0.le hhpi
  have hAgi : Integrable g (μ.restrict A) := hgi.integrableOn
  have hAci : Integrable c (μ.restrict A) := hci.integrableOn
  have hraw :
      (∫ θ,g θ ∂μ) -
        (∫ θ,cappedAngularCosine (2*Real.sin h/h) h θ * P θ ∂μ)
        = 2*(∫ θ in Ioc (0:ℝ) h,z θ) := by
    rw [hpiece,←hsplit]
    rw [integral_sub hAgi hAci] at hAeq
    linarith [hAeq]
  have hcomp := poissonKernel_comparator_centered hr0.le hr1
  rw [circleAverage_eq_restrictedAngularIntegral] at hcomp
  have hcmp : (2*Real.pi)⁻¹*(∫ θ,g θ ∂μ)=2*r := by
    change (2*Real.pi)⁻¹ *
      (∫ θ, P θ*(2*(circleMap 0 1 θ).re) ∂μ)=2*r at hcomp
    convert hcomp using 1
    congr 1
    apply integral_congr_ae
    filter_upwards [] with θ
    simp [g,circleMap_zero_re]
    ring
  change 2*r-(2*Real.pi)⁻¹*
    (∫ θ,cappedAngularCosine (2*Real.sin h/h) h θ*P θ ∂μ) =
      Real.pi⁻¹ * (∫ θ in Ioc (0:ℝ) h,z θ)
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hscale : (2*Real.pi)⁻¹*(2:ℝ)=Real.pi⁻¹ := by
    field_simp
  calc
    _ = (2*Real.pi)⁻¹ *
        ((∫ θ,g θ ∂μ)-
          (∫ θ,cappedAngularCosine (2*Real.sin h/h) h θ*P θ ∂μ)) := by
      rw [←hcmp]
      ring
    _ = Real.pi⁻¹ * (∫ θ in Ioc (0:ℝ) h,z θ) := by
      rw [hraw,←mul_assoc,hscale]

end SpringerLean

#print axioms SpringerLean.flattenedCosinePoisson_peak_defect_half_arc
