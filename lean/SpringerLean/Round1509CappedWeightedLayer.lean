import SpringerLean.Round1508AllPoissonLevels

open MeasureTheory Set Filter
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- Integrating the all-threshold inequality against the centered
Poisson kernel gives the regularized actual projection comparison,
with an explicit constant epsilon before passage to the limit. -/
theorem regularExterior_capped_poisson_weighted_difference_nonpos_eventually
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖=1) (h : ℝ)
    (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 2*Real.sin h/h)
    {ε : ℝ} (hε : 0 < ε)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n : ℕ in atTop,
      (∫ θ : ℝ,
        (((conj ξ*rescaleExterior (omittedScaleSeq n) F
            (circleMap 0 1 θ)).re -
          cappedAngularCosine (2*Real.sin h/h) h θ) - ε) *
          poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)
        ∂(volume.restrict (Ioc (0:ℝ) (2*Real.pi)))) ≤ 0 := by
  let μ : Measure ℝ := volume.restrict (Ioc (0:ℝ) (2*Real.pi))
  haveI : IsFiniteMeasure μ := Real.isFiniteMeasure_restrict_Ioc 0 (2*Real.pi)
  let u : ℝ → ℝ := cappedAngularCosine (2*Real.sin h/h) h
  let w : ℝ → ℝ := fun θ => poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)
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
      have hc := Real.abs_cos_le_one θ
      calc
        |2*Real.cos θ| = 2*|Real.cos θ| := by simp
        _ ≤ 2 := by nlinarith
        _ ≤ |2*Real.sin h/h|+2 := by linarith [abs_nonneg (2*Real.sin h/h)]
  have huInt : Integrable u μ := by
    apply Integrable.mono' (g := fun _ : ℝ => |2*Real.sin h/h|+2)
      (integrable_const _) huMeas.aestronglyMeasurable
    filter_upwards [] with θ
    simpa only [Real.norm_eq_abs] using huBound θ
  have hwMeas : Measurable w :=
    (centeredPoisson_weight_continuous hr0 hr1).measurable
  have hw0 (θ : ℝ) : 0 ≤ w θ :=
    (centeredPoisson_weight_bounds hr0 hr1 θ).1
  have hwM (θ : ℝ) : w θ ≤ (1-r^2)/(1-r)^2 :=
    (centeredPoisson_weight_bounds hr0 hr1 θ).2
  have he := regularExterior_all_poisson_levels_le_flattened_eventually
    F hc ξ hξ h hh0 hhpi hcap hε hr0 hr1
  filter_upwards [he] with n hn
  let f : ℝ → ℝ := fun θ =>
    (conj ξ*rescaleExterior (omittedScaleSeq n) F
      (circleMap 0 1 θ)).re
  let v : ℝ → ℝ := fun θ => (f θ-u θ)-ε
  obtain ⟨C,hC0,hC⟩ := regularExterior_projected_angle_bounded
    F hc (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n) ξ hξ
  have hfMeas : Measurable f := by
    exact (Complex.continuous_re.comp
      (regularExterior_rotated_angle_continuous F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n) ξ)).measurable
  have hfInt : Integrable f μ := by
    apply Integrable.mono' (g := fun _ : ℝ => C) (integrable_const C)
      hfMeas.aestronglyMeasurable
    filter_upwards [] with θ
    simpa only [Real.norm_eq_abs] using hC θ
  have hvMeas : Measurable v :=
    (hfMeas.sub huMeas).sub measurable_const
  have hB0 : 0 ≤ C+|2*Real.sin h/h|+2+ε := by positivity
  have hvBound (θ : ℝ) : |v θ| ≤ C+|2*Real.sin h/h|+2+ε := by
    dsimp [v]
    have h1 := abs_sub (f θ) (u θ)
    have h2 := abs_sub (f θ-u θ) ε
    have hf := hC θ
    have hu := huBound θ
    rw [abs_of_pos hε] at h2
    linarith
  have hlevels (t : ℝ) (ht : 0 < t)
      (_ : t ≤ (1-r^2)/(1-r)^2) :
      (∫ θ in {θ | t ≤ w θ}, v θ ∂μ) ≤ 0 := by
    let E : Set ℝ := {θ | t ≤ w θ}
    have hb := hn t ht
    change (∫ θ in E, f θ ∂μ) ≤
      (∫ θ in E, u θ ∂μ) + ε*μ.real E at hb
    have hEfin : μ E ≠ ⊤ := (measure_lt_top μ E).ne
    have hdInt : IntegrableOn (fun θ => f θ-u θ) E μ :=
      (hfInt.sub huInt).integrableOn
    have hdecomp : (∫ θ in E, (f θ-u θ)-ε ∂μ) =
        (∫ θ in E, f θ ∂μ) - (∫ θ in E, u θ ∂μ) -
          ε*μ.real E := by
      rw [integral_sub hdInt (integrableOn_const hEfin),
        integral_sub hfInt.integrableOn huInt.integrableOn,setIntegral_const]
      simp only [smul_eq_mul]
      ring
    change (∫ θ in E, (f θ-u θ)-ε ∂μ) ≤ 0
    rw [hdecomp]
    linarith
  exact bounded_weighted_integral_nonpos_of_levels
    μ v w hvMeas hwMeas (C+|2*Real.sin h/h|+2+ε)
      ((1-r^2)/(1-r)^2) hB0 hvBound hw0 hwM hlevels

end SpringerLean

#print axioms SpringerLean.regularExterior_capped_poisson_weighted_difference_nonpos_eventually
