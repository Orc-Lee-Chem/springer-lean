import SpringerLean.Round55DiskPolar
import SpringerLean.Round11PolarArea

open MeasureTheory

namespace SpringerLean

private theorem polarCoord_symm_eq_circleMap (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
  rw [← greenPolar_eq_polarCoord_symm, greenPolar, circleMap_zero]

/-- The angular window of the polar chart equals the normalized circle average. -/
theorem polar_angle_integral_eq_circleAverage (f : ℂ → ℝ) (r : ℝ) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        f (Complex.polarCoord.symm (r, θ)) ∂volume) =
      (2 * Real.pi) * Real.circleAverage f 0 r := by
  simp_rw [polarCoord_symm_eq_circleMap]
  have hp : Function.Periodic (fun θ : ℝ => f (circleMap 0 r θ)) (2 * Real.pi) :=
    fun θ => congrArg f (periodic_circleMap 0 r θ)
  have hshift :
      (∫ θ in -Real.pi..Real.pi, f (circleMap 0 r θ)) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap 0 r θ) := by
    simpa [show -Real.pi + 2 * Real.pi = Real.pi by ring]
      using (hp.intervalIntegral_add_eq (-Real.pi) 0)
  have hI : (∫ θ in Set.Ioo (-Real.pi) Real.pi,
      f (circleMap 0 r θ) ∂volume) =
      ∫ θ in -Real.pi..Real.pi, f (circleMap 0 r θ) := by
    rw [intervalIntegral.integral_of_le (by nlinarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo]
  rw [hI]
  rw [Real.circleAverage_def]
  simp only [smul_eq_mul]
  have hp0 : 2 * Real.pi ≠ 0 := by positivity
  rw [hshift]
  field_simp
/-- The actual filling's angular second-moment integral is sharply bounded. -/
theorem actualHarmonic_sq_angle_lintegral_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal
        (‖actualHarmonic F (Complex.polarCoord.symm (r, θ))‖ ^ 2)
      ∂volume) ≤ ENNReal.ofReal (4 * Real.pi * r ^ 2) := by
  let p : ℝ → ℂ := fun θ => Complex.polarCoord.symm (r, θ)
  let f : ℝ → ℝ := fun θ => ‖actualHarmonic F (p θ)‖ ^ 2
  have hpcont : Continuous p := by
    have hp : p = fun θ : ℝ =>
        (r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) := by
      funext θ
      exact Complex.polarCoord_symm_apply (r, θ)
    rw [hp]
    fun_prop
  have hpmem (θ : ℝ) : p θ ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [p, Metric.mem_ball, dist_zero_right,
      Complex.norm_polarCoord_symm, abs_of_pos hr0] using hr1
  have hfcont : Continuous f := by
    exact (((actualHarmonic_continuousOn_unitBall F hc).comp_continuous
      hpcont hpmem).norm).pow 2
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_nonneg]
  have hfint : IntegrableOn f (Set.Ioo (-Real.pi) Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hπ).mp
      (hfcont.intervalIntegrable (-Real.pi) Real.pi)
  have hlin :
      ENNReal.ofReal
        (∫ θ in Set.Ioo (-Real.pi) Real.pi, f θ ∂volume) =
      ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (f θ) ∂volume := by
    apply ofReal_integral_eq_lintegral_ofReal hfint
    filter_upwards [] with θ
    exact sq_nonneg _
  have hreal :
      (∫ θ in Set.Ioo (-Real.pi) Real.pi, f θ ∂volume) ≤
        4 * Real.pi * r ^ 2 := by
    change (∫ θ in Set.Ioo (-Real.pi) Real.pi,
      ‖actualHarmonic F (Complex.polarCoord.symm (r, θ))‖ ^ 2 ∂volume) ≤ _
    rw [polar_angle_integral_eq_circleAverage (fun z : ℂ => ‖actualHarmonic F z‖ ^ 2) r]
    have h := actualHarmonic_circle_energy_le_two F hc hr0 hr1
    have hp := Real.pi_pos
    nlinarith
  change (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal (f θ) ∂volume) ≤ _
  exact hlin ▸ ENNReal.ofReal_le_ofReal hreal

/-- The actual filling second moment has planar area at most π. -/
theorem actualHarmonic_sq_lintegral_le_pi
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    (∫⁻ z in Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (‖actualHarmonic F z‖ ^ 2) ∂volume) ≤
      ENNReal.ofReal Real.pi := by
  rw [actualHarmonic_sq_lintegral_polar F hc]
  have hradial :
      (∫⁻ r in Set.Ioo (0 : ℝ) 1,
        ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal r *
            ENNReal.ofReal
              (‖actualHarmonic F (Complex.polarCoord.symm (r, θ))‖ ^ 2)
          ∂volume ∂volume) ≤
      ∫⁻ r in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (4 * Real.pi * r ^ 3) ∂volume := by
    apply setLIntegral_mono
    · fun_prop
    · intro r hr
      have hangle := actualHarmonic_sq_angle_lintegral_le F hc hr.1 hr.2
      have hcont : Continuous (fun θ : ℝ =>
          ‖actualHarmonic F (Complex.polarCoord.symm (r, θ))‖ ^ 2) := by
        have hpcont : Continuous (fun θ : ℝ => Complex.polarCoord.symm (r, θ)) := by
          have hp : (fun θ : ℝ => Complex.polarCoord.symm (r, θ)) =
              fun θ : ℝ => (r : ℂ) *
                (Real.cos θ + Real.sin θ * Complex.I) := by
            funext θ
            exact Complex.polarCoord_symm_apply (r, θ)
          rw [hp]
          fun_prop
        have hmem (θ : ℝ) :
            Complex.polarCoord.symm (r, θ) ∈ Metric.ball (0 : ℂ) 1 := by
          simpa only [Metric.mem_ball, dist_zero_right,
            Complex.norm_polarCoord_symm, abs_of_pos hr.1] using hr.2
        exact (((actualHarmonic_continuousOn_unitBall F hc).comp_continuous
          hpcont hmem).norm).pow 2
      have hmeas : Measurable (fun θ : ℝ =>
          ENNReal.ofReal
            (‖actualHarmonic F (Complex.polarCoord.symm (r, θ))‖ ^ 2)) :=
        ENNReal.measurable_ofReal.comp hcont.measurable
      calc
        (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal r *
            ENNReal.ofReal
              (‖actualHarmonic F (Complex.polarCoord.symm (r, θ))‖ ^ 2)
          ∂volume) =
            ENNReal.ofReal r *
              (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
                ENNReal.ofReal
                  (‖actualHarmonic F (Complex.polarCoord.symm (r, θ))‖ ^ 2)
                ∂volume) := by
                  exact lintegral_const_mul (ENNReal.ofReal r) hmeas
        _ ≤ ENNReal.ofReal r * ENNReal.ofReal (4 * Real.pi * r ^ 2) :=
          by exact mul_le_mul_of_nonneg_left hangle (by positivity)
        _ = ENNReal.ofReal (4 * Real.pi * r ^ 3) := by
          rw [← ENNReal.ofReal_mul hr.1.le]
          congr 1
          ring
  have hreal :
      (∫ r in Set.Ioo (0 : ℝ) 1, 4 * Real.pi * r ^ 3 ∂volume) =
        Real.pi := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hmul :
        (∫ r in (0 : ℝ)..1, 4 * Real.pi * r ^ 3) =
          (4 * Real.pi) * ∫ r in (0 : ℝ)..1, r ^ 3 := by
      simpa only [mul_assoc] using
        (intervalIntegral.integral_const_mul (a := (0 : ℝ)) (b := 1)
          (r := 4 * Real.pi) (f := fun r : ℝ => r ^ 3))
    rw [hmul, integral_pow]
    ring
  have hcont : Continuous (fun r : ℝ => 4 * Real.pi * r ^ 3) := by fun_prop
  have hint : IntegrableOn (fun r : ℝ => 4 * Real.pi * r ^ 3)
      (Set.Ioo (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (hcont.intervalIntegrable 0 1)
  have hlin :
      (∫⁻ r in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (4 * Real.pi * r ^ 3) ∂volume) =
        ENNReal.ofReal Real.pi := by
    have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
        (fun r : ℝ => 4 * Real.pi * r ^ 3) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      have hr0 : 0 < r := hr.1
      positivity
    calc
      _ = ENNReal.ofReal
            (∫ r in Set.Ioo (0 : ℝ) 1, 4 * Real.pi * r ^ 3 ∂volume) :=
          (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
      _ = ENNReal.ofReal Real.pi := by rw [hreal]
  exact hradial.trans_eq hlin

/-- Sharp normalized second moment of the actual harmonic filling. -/
theorem actualHarmonicMoment_two_le_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualHarmonicMoment F 2 ≤ 1 := by
  have hint : IntegrableOn
      (fun z : ℂ => ‖actualHarmonic F z‖ ^ 2)
      (Metric.ball (0 : ℂ) 1) :=
    (actualHarmonic_weighted_integrableOn F hc 2).1
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Metric.ball (0 : ℂ) 1)]
        (fun z : ℂ => ‖actualHarmonic F z‖ ^ 2) := by
    filter_upwards [] with z
    exact sq_nonneg _
  have hlin := ofReal_integral_eq_lintegral_ofReal hint hnonneg
  have hbound := actualHarmonic_sq_lintegral_le_pi F hc
  have hreal :
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖actualHarmonic F z‖ ^ 2 ∂volume) ≤ Real.pi :=
    (ENNReal.ofReal_le_ofReal_iff Real.pi_nonneg).mp (hlin.le.trans hbound)
  change Real.pi⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖actualHarmonic F z‖ ^ 2 ∂volume) ≤ 1
  rw [← div_eq_inv_mul]
  exact (div_le_one Real.pi_pos).mpr hreal

/-- The first formerly open higher odd inverse coefficient bound, for every
actual centered exterior univalent map. -/
theorem exteriorInverseCoeff_three_norm_le_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorInverseCoeff F 3‖ ≤ 1 := by
  have hM : actualHarmonicMoment F 2 ≤ 1 :=
    actualHarmonicMoment_two_le_one F hc
  have hM0 : 0 ≤ actualHarmonicMoment F 2 := by
    unfold actualHarmonicMoment
    apply mul_nonneg (inv_nonneg.mpr Real.pi_nonneg)
    apply integral_nonneg
    intro z
    positivity
  have hA0 : 0 ≤ actualOmittedMoment F 2 := by
    unfold actualOmittedMoment
    apply mul_nonneg (inv_nonneg.mpr Real.pi_nonneg)
    apply integral_nonneg
    intro z
    positivity
  have hCS := exteriorInverseCoeff_odd_norm_sq_le_moment_product F hc
    (k := 2) (by norm_num)
  norm_num at hCS
  have hMA : 0 ≤ actualHarmonicMoment F 2 * actualOmittedMoment F 2 :=
    mul_nonneg hM0 hA0
  have hM2 : actualHarmonicMoment F 2 ^ 2 ≤ 1 := by nlinarith
  have hB2 : ‖exteriorInverseCoeff F 3‖ ^ 2 ≤ 1 := by nlinarith
  nlinarith [norm_nonneg (exteriorInverseCoeff F 3)]

end SpringerLean
