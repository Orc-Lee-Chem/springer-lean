import SpringerLean.Round58CircleRigidity
import SpringerLean.LowOrder
import SpringerLean.GeneralArea

open MeasureTheory

namespace SpringerLean

/-- The angular ENNReal second moment equals the normalized actual circle
average, including its 2π normalization. -/
theorem actualHarmonic_sq_angle_lintegral_eq_circleAverage
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal
        (‖actualHarmonic F (Complex.polarCoord.symm (r, θ))‖ ^ 2)
      ∂volume) =
      ENNReal.ofReal
        (2 * Real.pi * Real.circleAverage
          (fun z : ℂ => ‖actualHarmonic F z‖ ^ 2) 0 r) := by
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
  change (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal (f θ) ∂volume) = _
  rw [← hlin]
  congr 1
  exact polar_angle_integral_eq_circleAverage
    (fun z : ℂ => ‖actualHarmonic F z‖ ^ 2) r

/-- A coefficient-sensitive normalized second-moment bound; equality at
one forces saturation of the first forward coefficient. -/
theorem actualHarmonicMoment_two_le_firstCoeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualHarmonicMoment F 2 ≤
      (5 + ‖exteriorForwardCoeff F 1‖ ^ 2) / 6 := by
  let q : ℝ := ‖exteriorForwardCoeff F 1‖ ^ 2
  have hq0 : 0 ≤ q := sq_nonneg _
  have hq1 : q ≤ 1 := by
    have h := exteriorForwardCoeff_one_norm_le_of_finite_area F
      (fun N => exteriorForwardCoeff_finite_area F hc N)
    dsimp [q]
    nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]
  let B : ℝ → ℝ := fun r =>
    2 * Real.pi * (r ^ 3 * (1 + q) + r ^ 5 * (1 - q))
  have hpolar := actualHarmonic_sq_lintegral_polar F hc
  have hradial :
      (∫⁻ r in Set.Ioo (0 : ℝ) 1,
        ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal r *
            ENNReal.ofReal
              (‖actualHarmonic F (Complex.polarCoord.symm (r, θ))‖ ^ 2)
          ∂volume ∂volume) ≤
      ∫⁻ r in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (B r) ∂volume := by
    apply setLIntegral_mono
    · exact ENNReal.measurable_ofReal.comp (by fun_prop : Measurable B)
    · intro r hr
      have hCircle := actualHarmonic_circle_energy_eq F hc hr.1 hr.2
      have hForward := exteriorForwardGerm_circle_energy_le_firstCoeff
        F hc hr.1 hr.2
      have hAngle :
          (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal
              (‖actualHarmonic F (Complex.polarCoord.symm (r, θ))‖ ^ 2)
            ∂volume) ≤
          ENNReal.ofReal
            (2 * Real.pi *
              (r ^ 2 + r ^ 2 * q + r ^ 4 * (1 - q))) := by
        rw [actualHarmonic_sq_angle_lintegral_eq_circleAverage F hc hr.1 hr.2]
        apply ENNReal.ofReal_le_ofReal
        rw [hCircle]
        exact mul_le_mul_of_nonneg_left (by dsimp [q] at hForward ⊢; linarith)
          (by positivity : 0 ≤ 2 * Real.pi)
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
                ∂volume) :=
                  lintegral_const_mul (ENNReal.ofReal r) hmeas
        _ ≤ ENNReal.ofReal r *
              ENNReal.ofReal
                (2 * Real.pi *
                  (r ^ 2 + r ^ 2 * q + r ^ 4 * (1 - q))) :=
          mul_le_mul_of_nonneg_left hAngle (by positivity)
        _ = ENNReal.ofReal (B r) := by
          rw [← ENNReal.ofReal_mul hr.1.le]
          congr 1
          dsimp [B]
          ring
  have hcontB : Continuous B := by dsimp [B]; fun_prop
  have hintB : IntegrableOn B (Set.Ioo (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (hcontB.intervalIntegrable 0 1)
  have hreal : (∫ r in Set.Ioo (0 : ℝ) 1, B r ∂volume) =
      Real.pi * (5 + q) / 6 := by
    have h3 : (∫ r in Set.Ioo (0 : ℝ) 1, r ^ 3 ∂volume) = 1 / 4 := by
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_pow]
      norm_num
    have h5 : (∫ r in Set.Ioo (0 : ℝ) 1, r ^ 5 ∂volume) = 1 / 6 := by
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_pow]
      norm_num
    have hint3 : IntegrableOn (fun r : ℝ => r ^ 3) (Set.Ioo (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
        ((by fun_prop : Continuous (fun r : ℝ => r ^ 3)).intervalIntegrable 0 1)
    have hint5 : IntegrableOn (fun r : ℝ => r ^ 5) (Set.Ioo (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
        ((by fun_prop : Continuous (fun r : ℝ => r ^ 5)).intervalIntegrable 0 1)
    have hpoint (r : ℝ) : B r =
        (2 * Real.pi * (1 + q)) * r ^ 3 +
          (2 * Real.pi * (1 - q)) * r ^ 5 := by
      dsimp [B]
      ring
    simp_rw [hpoint]
    rw [integral_add (hint3.const_mul _) (hint5.const_mul _),
      integral_const_mul, integral_const_mul, h3, h5]
    ring
  have hBnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    dsimp [B]
    have hr0 : 0 ≤ r := hr.1.le
    have h1q : 0 ≤ 1 - q := by linarith
    positivity
  have hlin :
      (∫⁻ r in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (B r) ∂volume) =
        ENNReal.ofReal (Real.pi * (5 + q) / 6) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hintB hBnonneg, hreal]
  have hInt : IntegrableOn (fun z : ℂ => ‖actualHarmonic F z‖ ^ 2)
      (Metric.ball (0 : ℂ) 1) :=
    (actualHarmonic_weighted_integrableOn F hc 2).1
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Metric.ball (0 : ℂ) 1)]
        (fun z : ℂ => ‖actualHarmonic F z‖ ^ 2) := by
    filter_upwards [] with z
    exact sq_nonneg _
  have hlinDisk := ofReal_integral_eq_lintegral_ofReal hInt hnonneg
  have hBbound :
      ENNReal.ofReal
        (∫ z in Metric.ball (0 : ℂ) 1,
          ‖actualHarmonic F z‖ ^ 2 ∂volume) ≤
        ENNReal.ofReal (Real.pi * (5 + q) / 6) :=
    hlinDisk.le.trans (hpolar.le.trans (hradial.trans_eq hlin))
  have hBpos : 0 ≤ Real.pi * (5 + q) / 6 := by positivity
  have hrealBound :
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖actualHarmonic F z‖ ^ 2 ∂volume) ≤
        Real.pi * (5 + q) / 6 :=
    (ENNReal.ofReal_le_ofReal_iff hBpos).mp hBbound
  change Real.pi⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖actualHarmonic F z‖ ^ 2 ∂volume) ≤ (5 + q) / 6
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [← div_eq_inv_mul]
  exact (div_le_iff₀ hpi).mpr (by nlinarith [hrealBound])

/-- Saturating the actual filling second moment forces the first forward
coefficient to saturate the exterior area theorem. -/
theorem actualHarmonicMoment_two_eq_one_forwardCoeff_one_norm_eq_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hM : actualHarmonicMoment F 2 = 1) :
    ‖exteriorForwardCoeff F 1‖ = 1 := by
  have hq := actualHarmonicMoment_two_le_firstCoeff F hc
  rw [hM] at hq
  have hNorm := exteriorForwardCoeff_one_norm_le_of_finite_area F
    (fun N => exteriorForwardCoeff_finite_area F hc N)
  have hNonneg := norm_nonneg (exteriorForwardCoeff F 1)
  nlinarith

/-- Complete k=2 equality classification for the actual inverse
coefficient, with equality only on the paper's exterior domain. -/
theorem exteriorInverseCoeff_three_norm_eq_one_iff_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorInverseCoeff F 3‖ = 1 ↔
      ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk := by
  constructor
  · intro hB
    have hM := (exteriorInverseCoeff_three_eq_one_moment_saturation F hc hB).1
    have hcoef := actualHarmonicMoment_two_eq_one_forwardCoeff_one_norm_eq_one
      F hc hM
    have hB1 : ‖exteriorInverseCoeff F 1‖ = 1 := by
      rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc]
      exact hcoef
    exact (exteriorInverseCoeff_one_norm_eq_one_iff_slit F hc).mp hB1
  · rintro ⟨a, ha, hFG⟩
    have hca := slitMap_centeredExteriorUnivalent a ha
    have hCoeff : exteriorInverseCoeff F 3 =
        exteriorInverseCoeff (slitMap a) 3 := by
      rw [exteriorInverseCoeff_three_eq_forward F hc,
        exteriorInverseCoeff_three_eq_forward (slitMap a) hca]
      rw [exteriorForwardCoeff_eq_of_eqOn_exterior F (slitMap a) hFG 3,
        exteriorForwardCoeff_eq_of_eqOn_exterior F (slitMap a) hFG 1]
    rw [hCoeff, exteriorInverseCoeff_slitMap_three a ha]
    simp [norm_pow, ha]

end SpringerLean