import SpringerLean.Round11Partition

open MeasureTheory

namespace SpringerLean

/-- Rotating the angular integration window by one half-turn does not alter
the product integral of a `2π`-periodic real integrand. -/
theorem polar_rectangle_angle_shift
    (f : ℝ × ℝ → ℝ) (a b : ℝ)
    (hperiod : ∀ r θ : ℝ, f (r, θ + 2 * Real.pi) = f (r, θ))
    (hzero : IntegrableOn f
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)))
    (hneg : IntegrableOn f
      (Set.Icc a b ×ˢ Set.Icc (-Real.pi) Real.pi)) :
    (∫ p in Set.Icc (a, (0 : ℝ)) (b, 2 * Real.pi), f p ∂volume) =
      ∫ p in Set.Icc (a, -Real.pi) (b, Real.pi), f p ∂volume := by
  have houter : MeasurableSet (Set.Icc a b) := measurableSet_Icc
  have hzero' :
      (∫ p in Set.Icc (a, (0 : ℝ)) (b, 2 * Real.pi), f p ∂volume) =
      ∫ r in Set.Icc a b,
        ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), f (r, θ) ∂volume ∂volume := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    simpa using setIntegral_prod f hzero
  have hneg' :
      (∫ p in Set.Icc (a, -Real.pi) (b, Real.pi), f p ∂volume) =
      ∫ r in Set.Icc a b,
        ∫ θ in Set.Icc (-Real.pi) Real.pi, f (r, θ) ∂volume ∂volume := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    simpa using setIntegral_prod f hneg
  rw [hzero', hneg']
  apply setIntegral_congr_fun houter
  intro r hr
  have hp : Function.Periodic (fun θ : ℝ => f (r, θ)) (2 * Real.pi) :=
    fun θ => hperiod r θ
  have hshift := hp.intervalIntegral_add_eq (-(Real.pi)) 0
  have h₁ : -Real.pi ≤ -Real.pi + 2 * Real.pi := by
    nlinarith [Real.pi_pos]
  have h₂ : (0 : ℝ) ≤ 0 + 2 * Real.pi := by positivity
  rw [intervalIntegral.integral_of_le h₁,
    intervalIntegral.integral_of_le h₂] at hshift
  simpa [integral_Icc_eq_integral_Ioc,
    show -Real.pi + 2 * Real.pi = Real.pi by ring] using hshift.symm

/-- The open planar annulus (allowing inner radius zero) used by the signed
polar change of variables. -/
def greenPolarRegion (a b : ℝ) : Set ℂ :=
  {z | a < ‖z‖ ∧ ‖z‖ < b}

theorem greenPolarRegion_measurable (a b : ℝ) :
    MeasurableSet (greenPolarRegion a b) := by
  have h : IsOpen (greenPolarRegion a b) := by
    change IsOpen ((fun z : ℂ => ‖z‖) ⁻¹' Set.Ioo a b)
    exact isOpen_Ioo.preimage continuous_norm
  exact h.measurableSet

theorem greenPolarRegion_polar_preimage
    (a b : ℝ) (ha : 0 ≤ a) :
    Complex.polarCoord.target ∩
      (fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' greenPolarRegion a b =
      Set.Ioo a b ×ˢ Set.Ioo (-Real.pi) Real.pi := by
  ext p
  constructor
  · rintro ⟨hp, hregion⟩
    have hp0 : 0 < p.1 := by
      change p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi at hp
      exact hp.1
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      simpa [abs_of_pos hp0] using Complex.norm_polarCoord_symm p
    have hregion' : a < p.1 ∧ p.1 < b := by
      change a < ‖Complex.polarCoord.symm p‖ ∧
        ‖Complex.polarCoord.symm p‖ < b at hregion
      rw [hn] at hregion
      exact hregion
    exact ⟨hregion', hp.2⟩
  · rintro ⟨hr, hθ⟩
    have hp0 : 0 < p.1 := lt_of_le_of_lt ha hr.1
    have hp : p ∈ Complex.polarCoord.target := by
      change p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi
      exact ⟨hp0, hθ⟩
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      simpa [abs_of_pos hp0] using Complex.norm_polarCoord_symm p
    refine ⟨hp, ?_⟩
    change a < ‖Complex.polarCoord.symm p‖ ∧
      ‖Complex.polarCoord.symm p‖ < b
    rw [hn]
    exact hr

/-- Mathlib's signed complex polar change of variables, restricted to an
open annulus and retaining its native angular window `(-π,π)`. -/
theorem greenPolarRegion_integral_neg_angle
    (f : ℂ → ℝ) (a b : ℝ) (ha : 0 ≤ a) :
    (∫ z in greenPolarRegion a b, f z ∂volume) =
      ∫ p in Set.Ioo a b ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 * f (Complex.polarCoord.symm p) ∂volume := by
  let A : Set ℂ := greenPolarRegion a b
  let ψ : ℝ × ℝ → ℂ := fun p => Complex.polarCoord.symm p
  let q : ℝ × ℝ → ℝ := fun p => p.1 * f (ψ p)
  have hA : MeasurableSet A := greenPolarRegion_measurable a b
  have hψcont : Continuous ψ := by
    have heq : ψ = fun p : ℝ × ℝ =>
        (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
      funext p
      exact Complex.polarCoord_symm_apply p
    rw [heq]
    fun_prop
  have hψ : Measurable ψ := hψcont.measurable
  have hpre : MeasurableSet (ψ ⁻¹' A) := hA.preimage hψ
  have hindicator (p : ℝ × ℝ) :
      p.1 • A.indicator f (ψ p) =
        (ψ ⁻¹' A).indicator q p := by
    by_cases hp : ψ p ∈ A
    · simp [Set.indicator_of_mem, hp, q, smul_eq_mul]
    · simp [Set.indicator_of_notMem, hp, q]
  calc
    (∫ z in greenPolarRegion a b, f z ∂volume) =
        ∫ z, A.indicator f z ∂volume := by
          exact (integral_indicator hA).symm
    _ = ∫ p in Complex.polarCoord.target,
          p.1 • A.indicator f (ψ p) ∂volume := by
          exact (Complex.integral_comp_polarCoord_symm (A.indicator f)).symm
    _ = ∫ p in Complex.polarCoord.target,
          (ψ ⁻¹' A).indicator q p ∂volume := by
          apply setIntegral_congr_fun (by
            rw [Complex.polarCoord_target]
            exact measurableSet_Ioi.prod measurableSet_Ioo)
          intro p hp
          exact hindicator p
    _ = ∫ p in Complex.polarCoord.target ∩ ψ ⁻¹' A,
          q p ∂volume := by
          exact setIntegral_indicator hpre
    _ = ∫ p in Set.Ioo a b ×ˢ Set.Ioo (-Real.pi) Real.pi,
          q p ∂volume := by
          rw [greenPolarRegion_polar_preimage a b ha]
    _ = _ := rfl

/-- Signed polar area conversion in the same `0..2π` angular convention as
the Green boundary integral. The two explicit integrability hypotheses are
only for Fubini's angle shift and hold for the smooth compact rectangles in
the regularized application. -/
theorem greenPolarRegion_integral_positive_angle
    (f : ℂ → ℝ) (a b : ℝ) (ha : 0 ≤ a)
    (hzero : IntegrableOn
      (fun p : ℝ × ℝ => p.1 * f (greenPolar p.1 p.2))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)))
    (hneg : IntegrableOn
      (fun p : ℝ × ℝ => p.1 * f (greenPolar p.1 p.2))
      (Set.Icc a b ×ˢ Set.Icc (-Real.pi) Real.pi)) :
    (∫ p in Set.Icc (a, (0 : ℝ)) (b, 2 * Real.pi),
      p.1 * f (greenPolar p.1 p.2) ∂volume) =
      ∫ z in greenPolarRegion a b, f z ∂volume := by
  let q : ℝ × ℝ → ℝ := fun p => p.1 * f (greenPolar p.1 p.2)
  have hperiod : ∀ r θ : ℝ, q (r, θ + 2 * Real.pi) = q (r, θ) := by
    intro r θ
    simp [q, greenPolar_periodic]
  have hshift := polar_rectangle_angle_shift q a b hperiod hzero hneg
  have hae :
      (Set.Ioo a b ×ˢ Set.Ioo (-Real.pi) Real.pi : Set (ℝ × ℝ))
        =ᵐ[volume]
      (Set.Icc a b ×ˢ Set.Icc (-Real.pi) Real.pi : Set (ℝ × ℝ)) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  have hclosed :
      (∫ p in Set.Icc (a, -Real.pi) (b, Real.pi), q p ∂volume) =
      ∫ p in Set.Ioo a b ×ˢ Set.Ioo (-Real.pi) Real.pi,
        q p ∂volume := by
    simpa only [Set.Icc_prod_eq] using (setIntegral_congr_set hae.symm :
      (∫ p in Set.Icc a b ×ˢ Set.Icc (-Real.pi) Real.pi,
        q p ∂volume) =
      ∫ p in Set.Ioo a b ×ˢ Set.Ioo (-Real.pi) Real.pi,
        q p ∂volume)
  calc
    (∫ p in Set.Icc (a, (0 : ℝ)) (b, 2 * Real.pi),
        p.1 * f (greenPolar p.1 p.2) ∂volume) =
        ∫ p in Set.Icc (a, -Real.pi) (b, Real.pi), q p ∂volume := hshift
    _ = ∫ p in Set.Ioo a b ×ˢ Set.Ioo (-Real.pi) Real.pi,
          q p ∂volume := hclosed
    _ = ∫ z in greenPolarRegion a b, f z ∂volume := by
      simpa only [q, greenPolar_eq_polarCoord_symm] using
        (greenPolarRegion_integral_neg_angle f a b ha).symm

/-- A signed Jacobian pullback is integrable on a compact polar rectangle
whenever its plane map is C² at every point of that rectangle. -/
theorem green_signed_polar_integrableOn
    (φ : ℂ → ℝ) (hφ : Continuous φ)
    (W : ℂ → ℂ) (a b c d : ℝ)
    (hW : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d,
      ContDiffAt ℝ 2 W (greenPolar p.1 p.2)) :
    IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * φ (W (greenPolar p.1 p.2)) *
        (fderiv ℝ W (greenPolar p.1 p.2)).det)
      (Set.Icc a b ×ˢ Set.Icc c d) := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ =>
        p.1 * φ (W (greenPolar p.1 p.2)) *
          (fderiv ℝ W (greenPolar p.1 p.2)).det)
      (Set.Icc a b ×ˢ Set.Icc c d) := by
    apply continuousOn_of_forall_continuousAt
    intro p hp
    have hpolar : ContinuousAt
        (fun q : ℝ × ℝ => greenPolar q.1 q.2) p :=
      greenPolar_contDiff.continuous.continuousAt
    have hWcont : ContinuousAt W (greenPolar p.1 p.2) :=
      (hW p hp).continuousAt
    have hder : ContinuousAt (fderiv ℝ W) (greenPolar p.1 p.2) :=
      ((hW p hp).fderiv_right (m := 0) (by norm_num)).continuousAt
    have hWpolar : ContinuousAt
        (fun q : ℝ × ℝ => W (greenPolar q.1 q.2)) p :=
      ContinuousAt.comp' (f := fun q : ℝ × ℝ => greenPolar q.1 q.2)
        hWcont hpolar
    have hderpolar : ContinuousAt
        (fun q : ℝ × ℝ => fderiv ℝ W (greenPolar q.1 q.2)) p :=
      ContinuousAt.comp' (f := fun q : ℝ × ℝ => greenPolar q.1 q.2)
        hder hpolar
    have hφcomp : ContinuousAt
        (fun q : ℝ × ℝ => φ (W (greenPolar q.1 q.2))) p :=
      ContinuousAt.comp' hφ.continuousAt hWpolar
    have hdet : ContinuousAt
        (fun q : ℝ × ℝ =>
          (fderiv ℝ W (greenPolar q.1 q.2)).det) p :=
      ContinuousAt.comp' ContinuousLinearMap.continuous_det.continuousAt
        hderpolar
    exact ((continuous_fst.continuousAt.mul hφcomp).mul hdet)
  exact hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

/-- Signed planar area is the same as the positive-angle polar parameter
integral for a map C² on the relevant closed annulus. -/
theorem green_signed_polar_integral_eq_region
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (W : ℂ → ℂ) (a b : ℝ) (ha : 0 ≤ a)
    (hW : ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → ContDiffAt ℝ 2 W z) :
    (∫ p in Set.Icc (a, (0 : ℝ)) (b, 2 * Real.pi),
      p.1 * φ (W (greenPolar p.1 p.2)) *
        (fderiv ℝ W (greenPolar p.1 p.2)).det ∂volume) =
      ∫ z in greenPolarRegion a b,
        φ (W z) * (fderiv ℝ W z).det ∂volume := by
  let f : ℂ → ℝ := fun z => φ (W z) * (fderiv ℝ W z).det
  have hloc (c d : ℝ) :
      ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d,
        ContDiffAt ℝ 2 W (greenPolar p.1 p.2) := by
    intro p hp
    have hr0 : 0 ≤ p.1 := ha.trans hp.1.1
    apply hW (greenPolar p.1 p.2)
    · simpa [greenPolar_norm_of_nonneg hr0] using hp.1.1
    · simpa [greenPolar_norm_of_nonneg hr0] using hp.1.2
  have hzero := green_signed_polar_integrableOn φ hφ.continuous
    W a b 0 (2 * Real.pi) (hloc 0 (2 * Real.pi))
  have hneg := green_signed_polar_integrableOn φ hφ.continuous
    W a b (-Real.pi) Real.pi (hloc (-Real.pi) Real.pi)
  have h := greenPolarRegion_integral_positive_angle f a b ha
    (by simpa only [f, mul_assoc] using hzero)
    (by simpa only [f, mul_assoc] using hneg)
  simpa only [f, mul_assoc] using h

/-- The first actual polar Green application: the signed Jacobian of the
regularized harmonic filling integrates over the open unit disk. -/
theorem regular_green_disk_area
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ) :
    (∫ z in Metric.ball (0 : ℂ) 1,
      φ (regularHarmonic s F z) *
        (fderiv ℝ (regularHarmonic s F) z).det ∂volume) =
      greenBoundary φ (fun θ => regularHarmonic s F (greenPolar 1 θ)) := by
  have hpolar := green_signed_polar_integral_eq_region φ hφ
    (regularHarmonic s F) 0 1 (by norm_num)
    (fun z hz0 hz1 => regularHarmonic_contDiffAt_closedDisk
      F hc hs0 hs1 hz1)
  have hparam := regular_green_parameter_disk_signed
    F hc hs0 hs1 φ hφ hcompact
  have hregion : greenPolarRegion 0 1 =
      Metric.ball (0 : ℂ) 1 \ {0} := by
    ext z
    simp [greenPolarRegion, Metric.mem_ball, dist_zero_right,
      norm_pos_iff, and_comm]
  have hae : greenPolarRegion 0 1 =ᵐ[volume]
      Metric.ball (0 : ℂ) 1 := by
    rw [hregion]
    exact sdiff_null_ae_eq_self (measure_singleton (0 : ℂ))
  have hset :
      (∫ z in greenPolarRegion 0 1,
        φ (regularHarmonic s F z) *
          (fderiv ℝ (regularHarmonic s F) z).det ∂volume) =
      ∫ z in Metric.ball (0 : ℂ) 1,
        φ (regularHarmonic s F z) *
          (fderiv ℝ (regularHarmonic s F) z).det ∂volume :=
    setIntegral_congr_set hae
  exact hset.symm.trans (hpolar.symm.trans hparam)

/-- The second actual polar Green application: the regularized exterior
annulus contributes its signed real Jacobian and the two true boundary
circulations. -/
theorem regular_green_annulus_area
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {R : ℝ} (hR : 1 < R)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ) :
    (∫ z in exteriorAnnulus 1 R,
      φ (rescaleExterior s F z) *
        (fderiv ℝ (rescaleExterior s F) z).det ∂volume) =
      greenBoundary φ (fun θ => rescaleExterior s F (greenPolar R θ)) -
        greenBoundary φ (fun θ => rescaleExterior s F (greenPolar 1 θ)) := by
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z := by
    intro z hzE
    exact hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hzE)
  have hW : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ ≤ R →
      ContDiffAt ℝ 2 (rescaleExterior s F) z := by
    intro z hz1 hzR
    have hz : z ∈ exteriorAbove s := by
      change s < ‖z‖
      exact lt_of_lt_of_le hs1 hz1
    exact (rescaleExterior_analyticAt hs0 hF hz).restrictScalars.contDiffAt
  have hpolar := green_signed_polar_integral_eq_region φ hφ
    (rescaleExterior s F) 1 R (by norm_num) hW
  have hparam := regular_green_parameter_annulus_signed
    F hc hs0 hs1 hR φ hφ hcompact
  change (∫ z in greenPolarRegion 1 R,
      φ (rescaleExterior s F z) *
        (fderiv ℝ (rescaleExterior s F) z).det ∂volume) = _
  exact hpolar.symm.trans hparam

/-- The standard positively oriented circle computes the ordinary real
area integral of the weight over its disk. -/
theorem green_standard_disk_area
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ)
    (R : ℝ) (hR : 0 < R) :
    (∫ z in Metric.ball (0 : ℂ) R, φ z ∂volume) =
      greenBoundary φ (fun θ => greenPolar R θ) := by
  have hpolar := green_signed_polar_integral_eq_region φ hφ
    (fun z : ℂ => z) 0 R (by norm_num)
    (fun z hz0 hzR => contDiffAt_id)
  have hparam := green_parameter_standard_disk_radial φ hφ hcompact R hR.le
  have hregion : greenPolarRegion 0 R =
      Metric.ball (0 : ℂ) R \ {0} := by
    ext z
    simp [greenPolarRegion, Metric.mem_ball, dist_zero_right,
      norm_pos_iff, and_comm]
  have hae : greenPolarRegion 0 R =ᵐ[volume]
      Metric.ball (0 : ℂ) R := by
    rw [hregion]
    exact sdiff_null_ae_eq_self (measure_singleton (0 : ℂ))
  have hset :
      (∫ z in greenPolarRegion 0 R, φ z ∂volume) =
        ∫ z in Metric.ball (0 : ℂ) R, φ z ∂volume :=
    setIntegral_congr_set hae
  have hpolar' :
      (∫ p in Set.Icc ((0 : ℝ), (0 : ℝ)) (R, 2 * Real.pi),
        p.1 * φ (greenPolar p.1 p.2) ∂volume) =
      ∫ z in greenPolarRegion 0 R, φ z ∂volume := by
    simpa [ContinuousLinearMap.det] using hpolar
  exact hset.symm.trans (hpolar'.symm.trans hparam)

end SpringerLean
