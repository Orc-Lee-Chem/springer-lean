import SpringerLean.AngularENN

open MeasureTheory

namespace SpringerLean

/-- The finite area correction is a lower bound for the genuine image area
of every annulus strictly inside the exterior domain. -/
theorem exteriorAnnulus_image_area_finite_lower
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r R : ℝ} (hr : 1 < r) (hR : r < R) (N : ℕ) :
    ENNReal.ofReal
      (Real.pi *
        (R ^ 2 - r ^ 2 +
          ∑ j ∈ Finset.Icc 1 N,
            (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2 *
              ((r⁻¹) ^ (2 * j) - (R⁻¹) ^ (2 * j)))) ≤
      volume (F '' exteriorAnnulus r R) := by
  let q : ℝ → ℝ := fun ρ =>
    2 * ρ + ∑ j ∈ Finset.Icc 1 N,
      ‖exteriorForwardCoeff F j‖ ^ 2 *
        (2 * (j : ℝ) ^ 2 * (ρ⁻¹) ^ (2 * j + 1))
  have hrpos : 0 < r := by linarith
  have hrle : r ≤ R := hR.le
  have hqint : IntegrableOn q (Set.Ioo r R) :=
    exteriorRadialFiniteEnergy_integrableOn F hrpos hrle N
  have hqnonneg : ∀ ρ ∈ Set.Ioo r R, 0 ≤ q ρ := by
    intro ρ hρ
    have hρpos : 0 < ρ := lt_trans hrpos hρ.1
    have hsum : 0 ≤ ∑ j ∈ Finset.Icc 1 N,
        (j : ℝ) ^ 2 * ‖exteriorForwardCoeff F j‖ ^ 2 *
          (ρ⁻¹) ^ (2 * j + 2) := by
      apply Finset.sum_nonneg
      intro j hj
      positivity
    have heq := exteriorRadialFiniteEnergy_eq_modes F hρpos N
    change q ρ = _ at heq
    rw [heq]
    positivity
  have hqπint : IntegrableOn (fun ρ => Real.pi * q ρ) (Set.Ioo r R) :=
    hqint.const_mul _
  have hqπnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioo r R)]
      (fun ρ => Real.pi * q ρ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
    exact mul_nonneg Real.pi_nonneg (hqnonneg ρ hρ)
  have hlin :
      ENNReal.ofReal
        (∫ ρ in Set.Ioo r R, Real.pi * q ρ ∂volume) =
      ∫⁻ ρ in Set.Ioo r R,
        ENNReal.ofReal (Real.pi * q ρ) ∂volume :=
    ofReal_integral_eq_lintegral_ofReal hqπint hqπnonneg
  have hangularMeas (ρ : ℝ) (hρ : 1 < ρ) :
      Measurable (fun θ : ℝ =>
        ENNReal.ofReal
          (‖deriv F (exteriorCirclePoint ρ
            (θ : AddCircle (2 * Real.pi)))‖ ^ 2)) := by
    have hcoe : Continuous (fun θ : ℝ =>
        (θ : AddCircle (2 * Real.pi))) := by fun_prop
    have hcont :=
      (((actualCircleDerivative_continuous F hc hρ).comp hcoe).norm.pow 2)
    exact ENNReal.measurable_ofReal.comp hcont.measurable
  have hpoint (ρ : ℝ) (hρ : ρ ∈ Set.Ioo r R) :
      ENNReal.ofReal (Real.pi * q ρ) ≤
        ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal ρ *
            ENNReal.ofReal
              (‖deriv F (exteriorCirclePoint ρ
                (θ : AddCircle (2 * Real.pi)))‖ ^ 2) ∂volume := by
    have hρpos : 0 < ρ := lt_trans hrpos hρ.1
    have hρext : 1 < ρ := lt_trans hr hρ.1
    have hangle := exteriorDerivativeCircle_finite_lintegral_le F hc hρext N
    have heq := exteriorRadialFiniteEnergy_eq_modes F hρpos N
    change q ρ = _ at heq
    rw [heq]
    have hreal : Real.pi *
        (2 * ρ * (1 + ∑ j ∈ Finset.Icc 1 N,
          (j : ℝ) ^ 2 * ‖exteriorForwardCoeff F j‖ ^ 2 *
            (ρ⁻¹) ^ (2 * j + 2))) =
        ρ * ((2 * Real.pi) *
          (1 + ∑ j ∈ Finset.Icc 1 N,
            (j : ℝ) ^ 2 * ‖exteriorForwardCoeff F j‖ ^ 2 *
              (ρ⁻¹) ^ (2 * j + 2))) := by ring
    rw [hreal, ENNReal.ofReal_mul hρpos.le]
    calc
      ENNReal.ofReal ρ * ENNReal.ofReal
          ((2 * Real.pi) *
            (1 + ∑ j ∈ Finset.Icc 1 N,
              (j : ℝ) ^ 2 * ‖exteriorForwardCoeff F j‖ ^ 2 *
                (ρ⁻¹) ^ (2 * j + 2))) ≤
          ENNReal.ofReal ρ *
            (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
              ENNReal.ofReal
                (‖deriv F (exteriorCirclePoint ρ
                  (θ : AddCircle (2 * Real.pi)))‖ ^ 2) ∂volume) :=
            mul_le_mul_of_nonneg_left hangle bot_le
      _ = _ := by
        rw [← lintegral_const_mul _ (hangularMeas ρ hρext)]
  have harea := exteriorAnnulus_image_area_eq_deriv_sq F hc
    (r := r) (R := R) hr
  rw [exteriorAnnulus_deriv_sq_lintegral_polar F hc
    (r := r) (R := R) hr] at harea
  have houter :
      (∫⁻ ρ in Set.Ioo r R,
        ENNReal.ofReal (Real.pi * q ρ) ∂volume) ≤
      volume (F '' exteriorAnnulus r R) := by
    rw [← harea]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
    exact hpoint ρ hρ
  have hradial := exteriorRadialFiniteEnergy_integral F hrpos hrle N
  have hinterval :
      (∫ ρ in Set.Ioo r R, q ρ ∂volume) =
      R ^ 2 - r ^ 2 +
        ∑ j ∈ Finset.Icc 1 N,
          (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2 *
            ((r⁻¹) ^ (2 * j) - (R⁻¹) ^ (2 * j)) := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hrle]
    exact hradial
  rw [← hlin] at houter
  rw [integral_const_mul, hinterval] at houter
  exact houter

end SpringerLean
