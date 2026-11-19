import SpringerLean.Round1527PoissonArcAlgebra

open MeasureTheory Set

namespace SpringerLean
set_option maxHeartbeats 640000

/-- Integrating the local Poisson/cosine identity over the positive
half of the cap arc produces only its Poisson mass and length. -/
theorem centeredPoisson_arc_defect_integral
    {r h d : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hh0 : 0 ≤ h) :
    (∫ θ in Ioc (0:ℝ) h,
      (d-2*(1-Real.cos θ))*
        poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)) =
      (d+(1-r)^2/r)*
        (∫ θ in Ioc (0:ℝ) h,
          poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)) -
        (1-r^2)*h/r := by
  let I : Set ℝ := Ioc 0 h
  let P : ℝ → ℝ := fun θ => poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)
  let μ : Measure ℝ := volume.restrict I
  have hPc : Continuous P := centeredPoisson_weight_continuous hr0 hr1
  have hPInt : Integrable P μ := by
    change IntegrableOn P I
    exact (hPc.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hconst : Integrable (fun _ : ℝ => (1-r^2)/r) μ := integrable_const _
  have hpoint (θ : ℝ) :
      (d-2*(1-Real.cos θ))*P θ =
        (d+(1-r)^2/r)*P θ-(1-r^2)/r := by
    have hid := centeredPoisson_cosine_defect_identity hr0 hr1 θ
    change 2*(1-Real.cos θ)*P θ =
      (1-r^2)/r-(1-r)^2/r*P θ at hid
    linarith only [hid]
  change (∫ θ, (d-2*(1-Real.cos θ))*P θ ∂μ) =
    (d+(1-r)^2/r)*(∫ θ,P θ ∂μ)-(1-r^2)*h/r
  simp_rw [hpoint]
  rw [integral_sub (hPInt.const_mul _) hconst,integral_const_mul]
  have hvol : μ.real Set.univ = h := by
    dsimp [μ,I]
    rw [Measure.real_def,Measure.restrict_apply MeasurableSet.univ,
      univ_inter,Real.volume_Ioc,sub_zero,ENNReal.toReal_ofReal hh0]
  rw [integral_const,smul_eq_mul,hvol]
  ring

end SpringerLean

#print axioms SpringerLean.centeredPoisson_arc_defect_integral
