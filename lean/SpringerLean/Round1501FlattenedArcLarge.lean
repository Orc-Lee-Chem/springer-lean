import SpringerLean.Round1500FlattenedArcSmall

open MeasureTheory Set

namespace SpringerLean

/-- On every arc containing the whole plateau, its mean-preserving
replacement changes no integral. -/
theorem cappedAngularCosine_large_arc_integral
    {h q R : ℝ} (hh0 : 0 < h) (hhq : h ≤ q)
    (hqpi : q < Real.pi) (hbalance : 2*h*R=4*Real.sin h) :
    (∫ θ in centeredAngularArc q, cappedAngularCosine R h θ) =
      4*Real.sin q := by
  classical
  let A : Set ℝ := centeredAngularArc h
  let B : Set ℝ := centeredAngularArc q
  let μ : Measure ℝ := volume.restrict B
  let g : ℝ → ℝ := fun θ => 2*Real.cos θ
  have hAmeas : MeasurableSet A := measurableSet_Ioc.union measurableSet_Icc
  have hBmeas : MeasurableSet B := measurableSet_Ioc.union measurableSet_Icc
  have hsub : A ⊆ B := centeredAngularArc_mono hhq
  have hvol : volume B < ⊤ := by
    change volume (centeredAngularArc q) < ⊤
    rw [centeredAngularArc_volume q (hh0.le.trans hhq) hqpi]
    exact ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hvol.ne
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
      centeredAngularArc_volume h hh0.le (hhq.trans_lt hqpi),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*h)]
    simp only [smul_eq_mul]
  have hcosA : (∫ θ in A, g θ ∂μ) = 4*Real.sin h := by
    have hr : (∫ θ in A, g θ ∂μ) = ∫ θ in A, g θ := by
      dsimp [μ]
      rw [Measure.restrict_restrict_of_subset hsub]
    rw [hr]
    exact centeredAngularArc_comparator_integral h hh0.le (hhq.trans_lt hqpi)
  have hcosB : (∫ θ, g θ ∂μ) = 4*Real.sin q :=
    centeredAngularArc_comparator_integral q (hh0.le.trans hhq) hqpi
  have hsplit := integral_add_compl (μ := μ) hAmeas hgInt
  have hmodel : (∫ θ, cappedAngularCosine R h θ ∂μ) =
      ∫ θ, g θ ∂μ := by
    rw [hpiece,←hsplit]
    linarith
  exact hmodel.trans hcosB

end SpringerLean

#print axioms SpringerLean.cappedAngularCosine_large_arc_integral
