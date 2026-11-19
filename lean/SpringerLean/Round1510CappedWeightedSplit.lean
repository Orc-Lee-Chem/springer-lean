import SpringerLean.Round1509CappedWeightedLayer

open MeasureTheory Set Filter
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- Separating the Poisson-weighted actual projection, flattened model
and explicit error from the kernel-checked layer-cake inequality. -/
theorem regularExterior_capped_weighted_integral_le_eventually
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖=1) (h : ℝ)
    (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 2*Real.sin h/h)
    {ε : ℝ} (hε : 0 < ε)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n : ℕ in atTop,
      (∫ θ : ℝ,
        (conj ξ*rescaleExterior (omittedScaleSeq n) F
          (circleMap 0 1 θ)).re *
          poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)
        ∂(volume.restrict (Ioc (0:ℝ) (2*Real.pi)))) ≤
      (∫ θ : ℝ,
        cappedAngularCosine (2*Real.sin h/h) h θ *
          poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)
        ∂(volume.restrict (Ioc (0:ℝ) (2*Real.pi)))) +
      ε*(∫ θ : ℝ,
        poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)
          ∂(volume.restrict (Ioc (0:ℝ) (2*Real.pi)))) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0:ℝ) (2*Real.pi))
  haveI : IsFiniteMeasure μ := Real.isFiniteMeasure_restrict_Ioc 0 (2*Real.pi)
  let u : ℝ → ℝ := cappedAngularCosine (2*Real.sin h/h) h
  let P : ℝ → ℝ := fun θ => poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)
  let M : ℝ := (1-r^2)/(1-r)^2
  have hPc : Continuous P := centeredPoisson_weight_continuous hr0 hr1
  have hPInt : Integrable P μ := by
    change IntegrableOn P (Ioc 0 (2*Real.pi))
    exact hPc.continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  have hP0 (θ : ℝ) : 0 ≤ P θ := (centeredPoisson_weight_bounds hr0 hr1 θ).1
  have hPM (θ : ℝ) : P θ ≤ M := (centeredPoisson_weight_bounds hr0 hr1 θ).2
  have huMeas : Measurable u := by
    dsimp [u,cappedAngularCosine]
    exact Measurable.ite (measurableSet_Ioc.union measurableSet_Icc)
      measurable_const (by fun_prop)
  have huBound (θ : ℝ) : |u θ| ≤ |2*Real.sin h/h|+2 := by
    classical
    by_cases hθ : θ ∈ centeredAngularArc h
    · simp only [u,cappedAngularCosine,if_pos hθ]
      linarith
    · simp only [u,cappedAngularCosine,if_neg hθ]
      calc
        |2*Real.cos θ| = 2*|Real.cos θ| := by simp
        _ ≤ 2 := by nlinarith [Real.abs_cos_le_one θ]
        _ ≤ |2*Real.sin h/h|+2 := by linarith [abs_nonneg (2*Real.sin h/h)]
  have hM0 : 0 ≤ M := by
    have hs : 0 < (1-r)^2 := sq_pos_of_pos (sub_pos.mpr hr1)
    have hn : 0 < 1-r^2 := by nlinarith
    exact div_nonneg hn.le hs.le
  have huPInt : Integrable (fun θ => u θ*P θ) μ := by
    apply Integrable.mono' (g := fun _ : ℝ => (|2*Real.sin h/h|+2)*M)
      (integrable_const _) (huMeas.mul hPc.measurable).aestronglyMeasurable
    filter_upwards [] with θ
    change |u θ * P θ| ≤ (|2*Real.sin h/h|+2)*M
    rw [abs_mul,abs_of_nonneg (hP0 θ)]
    calc
      |u θ| * P θ ≤ (|2*Real.sin h/h|+2)*P θ :=
        mul_le_mul_of_nonneg_right (huBound θ) (hP0 θ)
      _ ≤ (|2*Real.sin h/h|+2)*M :=
        mul_le_mul_of_nonneg_left (hPM θ) (by positivity)
  have he := regularExterior_capped_poisson_weighted_difference_nonpos_eventually
    F hc ξ hξ h hh0 hhpi hcap hε hr0 hr1
  filter_upwards [he] with n hn
  let f : ℝ → ℝ := fun θ =>
    (conj ξ*rescaleExterior (omittedScaleSeq n) F
      (circleMap 0 1 θ)).re
  have hfc : Continuous f :=
    Complex.continuous_re.comp (regularExterior_rotated_angle_continuous
      F hc (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n) ξ)
  have hfPInt : Integrable (fun θ => f θ*P θ) μ := by
    change IntegrableOn (fun θ => f θ*P θ) (Ioc 0 (2*Real.pi))
    exact ((hfc.mul hPc).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hsplit :
      (∫ θ, ((f θ-u θ)-ε)*P θ ∂μ) =
      (∫ θ, f θ*P θ ∂μ) - (∫ θ,u θ*P θ ∂μ) -
        ε*(∫ θ,P θ ∂μ) := by
    calc
      _ = ∫ θ, (f θ*P θ-u θ*P θ)-ε*P θ ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with θ
        ring
      _ = (∫ θ, f θ*P θ ∂μ) - (∫ θ,u θ*P θ ∂μ) -
          (∫ θ, ε*P θ ∂μ) := by
        have h1 : (∫ θ, (f θ*P θ-u θ*P θ)-ε*P θ ∂μ) =
            (∫ θ, f θ*P θ-u θ*P θ ∂μ) -
              (∫ θ, ε*P θ ∂μ) :=
          integral_sub (hfPInt.sub huPInt) (hPInt.const_mul ε)
        have h2 : (∫ θ, f θ*P θ-u θ*P θ ∂μ) =
            (∫ θ, f θ*P θ ∂μ) - (∫ θ,u θ*P θ ∂μ) :=
          integral_sub hfPInt huPInt
        rw [h1,h2]
      _ = _ := by rw [integral_const_mul]
  change (∫ θ, ((f θ-u θ)-ε)*P θ ∂μ) ≤ 0 at hn
  rw [hsplit] at hn
  change (∫ θ, f θ*P θ ∂μ) ≤
    (∫ θ,u θ*P θ ∂μ)+ε*(∫ θ,P θ ∂μ)
  linarith

end SpringerLean

#print axioms SpringerLean.regularExterior_capped_weighted_integral_le_eventually
