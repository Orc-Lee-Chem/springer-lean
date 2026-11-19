import SpringerLean.Round11CS
import Mathlib.Analysis.Complex.Polynomial.Basic

open MeasureTheory
open scoped ComplexConjugate

namespace SpringerLean

/-- Pointwise algebra of the real gradient of the imaginary part of a
harmonic complex field. This identity isolates the cross term that the
first area formula reads as the inverse coefficient. -/
theorem phase_gradient_coordinate_algebra (W d : ℂ) :
    (W * (1 + d)).im ^ 2 + (W * (1 - d)).re ^ 2 =
      ‖W‖ ^ 2 * (1 + ‖d‖ ^ 2) - 2 * (W ^ 2 * d).re := by
  rcases W with ⟨x, y⟩
  rcases d with ⟨a, b⟩
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im]
  simp only [pow_two, Complex.mul_re, Complex.mul_im]
  ring

/-- The actual harmonic filling has the expected real derivative at every
interior disk point, using the derivative of the original forward germ. -/
theorem actualHarmonic_hasFDerivAt_real
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasFDerivAt (actualHarmonic F)
      ((1 : ℂ →L[ℝ] ℂ) +
        ((deriv (exteriorForwardGerm F) (conj z)) •
          (1 : ℂ →L[ℝ] ℂ)).comp
          Complex.conjCLE.toContinuousLinearMap) z := by
  have hzc : conj z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right,
      ← Complex.star_def, norm_star] using hz
  have ha : AnalyticAt ℂ (exteriorForwardGerm F) (conj z) :=
    exteriorForwardGerm_analyticOnNhd_unitBall F hc (conj z) hzc
  have hg : HasDerivAt (exteriorForwardGerm F)
      (deriv (exteriorForwardGerm F) (conj z)) (conj z) :=
    ha.differentiableAt.hasDerivAt
  have hconj : HasFDerivAt (fun u : ℂ => conj u)
      Complex.conjCLE.toContinuousLinearMap z := by
    convert (Complex.conjCLE.hasFDerivAt (x := z)) using 1
    funext u
    simp
  have hcomp := hg.complexToReal_fderiv.comp z hconj
  have hsum := (hasFDerivAt_id z).add hcomp
  convert hsum using 1
  funext u
  simp [actualHarmonic, Function.comp_def, Pi.add_apply]

/-- The paper's phase field is the imaginary part of the actual filling. -/
noncomputable def actualHarmonicPhaseField
    (F : ℂ → ℂ) (k : ℕ) (β : ℂ) (z : ℂ) : ℝ :=
  (β * (actualHarmonic F z) ^ k).im

theorem actualHarmonicPhaseField_hasFDerivAt
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (β : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasFDerivAt (actualHarmonicPhaseField F k β)
      (Complex.imCLM.comp
        (((k : ℂ) * β * (actualHarmonic F z) ^ (k - 1)) •
          ((1 : ℂ →L[ℝ] ℂ) +
            ((deriv (exteriorForwardGerm F) (conj z)) •
              (1 : ℂ →L[ℝ] ℂ)).comp
              Complex.conjCLE.toContinuousLinearMap))) z := by
  have hH := actualHarmonic_hasFDerivAt_real F hc hz
  have hpow := hH.pow k
  have hphase := hpow.const_mul β
  have him := (Complex.imCLM.hasFDerivAt (x :=
    β * (actualHarmonic F z) ^ k)).comp z hphase
  convert him using 1
  · funext u
    rfl
  · ext v
    simp [mul_assoc, mul_comm, mul_left_comm]

/-- The two actual real coordinate derivatives of the phase field. -/
theorem actualHarmonicPhaseField_gradient_coordinates
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (β : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (fderiv ℝ (actualHarmonicPhaseField F k β) z) (1 : ℂ) =
      (((k : ℂ) * β * (actualHarmonic F z) ^ (k - 1)) *
        (1 + deriv (exteriorForwardGerm F) (conj z))).im ∧
    (fderiv ℝ (actualHarmonicPhaseField F k β) z) Complex.I =
      (((k : ℂ) * β * (actualHarmonic F z) ^ (k - 1)) *
        (1 - deriv (exteriorForwardGerm F) (conj z))).re := by
  have h := (actualHarmonicPhaseField_hasFDerivAt F hc k β hz).fderiv
  constructor
  · rw [h]
    simp [Complex.imCLM_apply, mul_add, mul_assoc]
  · rw [h]
    simp [Complex.imCLM_apply, Complex.conj_I,
      Complex.mul_im, Complex.mul_re]
    ring

/-- Pointwise Dirichlet-density expansion for the actual phase field. -/
theorem actualHarmonicPhaseField_gradient_sq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {k : ℕ} (hk : 1 ≤ k) (β : ℂ) (hβ : ‖β‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ((fderiv ℝ (actualHarmonicPhaseField F k β) z) (1 : ℂ)) ^ 2 +
      ((fderiv ℝ (actualHarmonicPhaseField F k β) z) Complex.I) ^ 2 =
      (k : ℝ) ^ 2 * ‖actualHarmonic F z‖ ^ (2 * k - 2) *
        (1 + ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2) -
      2 * (k : ℝ) ^ 2 *
        (β ^ 2 * (actualHarmonic F z) ^ (2 * k - 2) *
          deriv (exteriorForwardGerm F) (conj z)).re := by
  let H : ℂ := actualHarmonic F z
  let d : ℂ := deriv (exteriorForwardGerm F) (conj z)
  let W : ℂ := (k : ℂ) * β * H ^ (k - 1)
  obtain ⟨hx, hy⟩ := actualHarmonicPhaseField_gradient_coordinates
    F hc k β hz
  rw [hx, hy]
  have hbase := phase_gradient_coordinate_algebra W d
  have hm : (k - 1) * 2 = 2 * k - 2 := by omega
  have hWnorm : ‖W‖ ^ 2 = (k : ℝ) ^ 2 * ‖H‖ ^ (2 * k - 2) := by
    dsimp only [W]
    rw [norm_mul, norm_mul, hβ, mul_one, norm_pow, mul_pow, ← pow_mul, hm]
    simp
  have hWcross : (W ^ 2 * d).re =
      (k : ℝ) ^ 2 * (β ^ 2 * H ^ (2 * k - 2) * d).re := by
    have heq : W ^ 2 * d =
        ((k : ℂ) ^ 2) * (β ^ 2 * H ^ (2 * k - 2) * d) := by
      dsimp only [W]
      rw [mul_pow, mul_pow, ← pow_mul, hm]
      ring
    rw [heq, Complex.mul_re]
    have hre : ((k : ℂ) ^ 2).re = (k : ℝ) ^ 2 := by norm_cast
    have him : ((k : ℂ) ^ 2).im = 0 := by
      rw [pow_two, Complex.mul_im]
      simp
    rw [hre, him]
    ring
  rw [hWnorm, hWcross] at hbase
  simpa only [W, H, d, mul_assoc] using hbase

/-- Normalized Dirichlet energy of the actual real phase field. The two
directions `1` and `I` are the standard real-coordinate basis of `ℂ`. -/
noncomputable def actualHarmonicPhaseEnergy
    (F : ℂ → ℂ) (k : ℕ) (β : ℂ) : ℝ :=
  (Real.pi : ℝ)⁻¹ *
    (∫ z in Metric.ball (0 : ℂ) 1,
      ((fderiv ℝ (actualHarmonicPhaseField F k β) z) (1 : ℂ)) ^ 2 +
        ((fderiv ℝ (actualHarmonicPhaseField F k β) z) Complex.I) ^ 2
      ∂volume)

/-- The actual complex cross term in the phase-gradient expansion is
integrable on the unit disk. -/
theorem actualHarmonic_phase_cross_complex_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (m : ℕ) (β : ℂ) :
    IntegrableOn (fun z : ℂ =>
      β ^ 2 * actualHarmonic F z ^ m *
        deriv (exteriorForwardGerm F) (conj z))
      (Metric.ball (0 : ℂ) 1) := by
  let D : Set ℂ := Metric.ball 0 1
  let μ : Measure ℂ := volume.restrict D
  obtain ⟨C, hC0, hC⟩ := exteriorForwardGerm_bounded_unitDisk F hc
  have hH : ContinuousOn (actualHarmonic F) D :=
    actualHarmonic_continuousOn_unitBall F hc
  have hd : Integrable (fun z : ℂ =>
      deriv (exteriorForwardGerm F) (conj z)) μ :=
    exteriorForwardGerm_deriv_integrableOn F hc
  have hbound : ∀ᵐ z ∂μ,
      ‖β ^ 2 * actualHarmonic F z ^ m‖ ≤
        ‖β‖ ^ 2 * (1 + C) ^ m := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    have hz1 : ‖z‖ < 1 := by
      simpa only [D, Metric.mem_ball, dist_zero_right] using hz
    have hcz : ‖conj z‖ < 1 := by
      simpa only [Complex.norm_conj] using hz1
    have hHz : ‖actualHarmonic F z‖ ≤ 1 + C := by
      dsimp only [actualHarmonic]
      calc
        ‖z + exteriorForwardGerm F (conj z)‖ ≤
            ‖z‖ + ‖exteriorForwardGerm F (conj z)‖ := norm_add_le _ _
        _ ≤ 1 + C := by linarith [hC (conj z) hcz]
    rw [norm_mul, norm_pow, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hHz m) (sq_nonneg _)
  have hmeas : AEStronglyMeasurable
      (fun z : ℂ => β ^ 2 * actualHarmonic F z ^ m) μ :=
    ((continuousOn_const.mul (hH.pow m)).aestronglyMeasurable
      Metric.isOpen_ball.measurableSet)
  have hcplx : Integrable
      (fun z : ℂ => (β ^ 2 * actualHarmonic F z ^ m) *
        deriv (exteriorForwardGerm F) (conj z)) μ :=
    hd.bdd_mul hmeas hbound
  exact hcplx

theorem actualHarmonic_phase_cross_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (m : ℕ) (β : ℂ) :
    IntegrableOn (fun z : ℂ =>
      (β ^ 2 * actualHarmonic F z ^ m *
        deriv (exteriorForwardGerm F) (conj z)).re)
      (Metric.ball (0 : ℂ) 1) :=
  (actualHarmonic_phase_cross_complex_integrableOn F hc m β).re

/-- Integration of the actual coordinate-gradient identity. The remaining
complex cross integral is kept explicit for coefficient identification. -/
theorem actualHarmonicPhaseEnergy_eq_integrals
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {k : ℕ} (hk : 1 ≤ k) (β : ℂ) (hβ : ‖β‖ = 1) :
    actualHarmonicPhaseEnergy F k β =
      (k : ℝ) ^ 2 *
        ((Real.pi : ℝ)⁻¹ *
          (∫ z in Metric.ball (0 : ℂ) 1,
            ‖actualHarmonic F z‖ ^ (2 * k - 2) ∂volume) +
         (Real.pi : ℝ)⁻¹ *
          (∫ z in Metric.ball (0 : ℂ) 1,
            ‖actualHarmonic F z‖ ^ (2 * k - 2) *
              ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2 ∂volume)) -
      2 * (k : ℝ) ^ 2 * (Real.pi : ℝ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          (β ^ 2 * actualHarmonic F z ^ (2 * k - 2) *
            deriv (exteriorForwardGerm F) (conj z)).re ∂volume) := by
  let D : Set ℂ := Metric.ball 0 1
  let m : ℕ := 2 * k - 2
  let w : ℂ → ℝ := fun z => ‖actualHarmonic F z‖ ^ m
  let d2 : ℂ → ℝ := fun z =>
    ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2
  let c : ℂ → ℝ := fun z =>
    (β ^ 2 * actualHarmonic F z ^ m *
      deriv (exteriorForwardGerm F) (conj z)).re
  obtain ⟨hw, hwd⟩ := actualHarmonic_weighted_integrableOn F hc m
  have hcInt : IntegrableOn c D :=
    actualHarmonic_phase_cross_integrableOn F hc m β
  have hsumInt : IntegrableOn (fun z => w z * (1 + d2 z)) D := by
    have h := hw.add hwd
    convert h using 1
    funext z
    dsimp only [w, d2]
    simp only [Pi.add_apply]
    ring
  have hfirstInt : IntegrableOn
      (fun z => (k : ℝ) ^ 2 * (w z * (1 + d2 z))) D :=
    hsumInt.const_mul _
  have hsecondInt : IntegrableOn
      (fun z => (2 * (k : ℝ) ^ 2) * c z) D :=
    hcInt.const_mul _
  have hsumIntegral :
      (∫ z in D, w z * (1 + d2 z) ∂volume) =
      (∫ z in D, w z ∂volume) +
        (∫ z in D, w z * d2 z ∂volume) := by
    have hpoint : (∫ z in D, w z * (1 + d2 z) ∂volume) =
        ∫ z in D, w z + w z * d2 z ∂volume := by
      apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      intro z hz
      ring
    rw [hpoint]
    exact integral_add hw hwd
  have hpoint :
      (∫ z in D,
        ((fderiv ℝ (actualHarmonicPhaseField F k β) z) (1 : ℂ)) ^ 2 +
          ((fderiv ℝ (actualHarmonicPhaseField F k β) z) Complex.I) ^ 2
        ∂volume) =
      ∫ z in D,
        (k : ℝ) ^ 2 * (w z * (1 + d2 z)) -
          (2 * (k : ℝ) ^ 2) * c z ∂volume := by
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro z hz
    have hz1 : ‖z‖ < 1 := by
      simpa only [D, Metric.mem_ball, dist_zero_right] using hz
    simpa only [w, d2, c, m, mul_assoc] using
      (actualHarmonicPhaseField_gradient_sq F hc hk β hβ hz1)
  dsimp only [actualHarmonicPhaseEnergy]
  rw [hpoint, integral_sub hfirstInt hsecondInt,
    integral_const_mul, integral_const_mul, hsumIntegral]
  dsimp only [D, w, d2, c, m]
  ring

/-- The cross term in the actual phase energy is exactly the real part of
the original inverse coefficient after normalization. -/
theorem actualHarmonic_phase_cross_eq_inverseCoeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {k : ℕ} (hk : 1 ≤ k) (β : ℂ) :
    (Real.pi : ℝ)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        (β ^ 2 * actualHarmonic F z ^ (2 * k - 2) *
          deriv (exteriorForwardGerm F) (conj z)).re ∂volume) =
    (β ^ 2 * exteriorInverseCoeff F (2 * k - 1)).re := by
  let G : ℂ → ℂ := fun z =>
    actualHarmonic F z ^ (2 * k - 2) *
      deriv (exteriorForwardGerm F) (conj z)
  have hB : exteriorInverseCoeff F (2 * k - 1) =
      (Real.pi : ℂ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1, G z ∂volume) := by
    simpa only [G, actualHarmonic] using
      (exteriorInverseCoeff_odd_eq_actualHarmonic_diskIntegral F hc hk)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hBG : (∫ z in Metric.ball (0 : ℂ) 1, G z ∂volume) =
      (Real.pi : ℂ) * exteriorInverseCoeff F (2 * k - 1) := by
    rw [hB]
    field_simp [hpi]
  have hReal :
      (∫ z in Metric.ball (0 : ℂ) 1,
        (β ^ 2 * G z).re ∂volume) =
      (β ^ 2 * (∫ z in Metric.ball (0 : ℂ) 1,
        G z ∂volume)).re := by
    have hInt : IntegrableOn (fun z : ℂ => β ^ 2 * G z)
        (Metric.ball (0 : ℂ) 1) := by
      convert actualHarmonic_phase_cross_complex_integrableOn
        F hc (2 * k - 2) β using 1
      funext z
      dsimp only [G]
      ring
    calc
      (∫ z in Metric.ball (0 : ℂ) 1,
        (β ^ 2 * G z).re ∂volume) =
          (∫ z in Metric.ball (0 : ℂ) 1,
            β ^ 2 * G z ∂volume).re := by
              simpa only [RCLike.re_eq_complex_re] using (integral_re hInt)
      _ = (β ^ 2 * (∫ z in Metric.ball (0 : ℂ) 1,
          G z ∂volume)).re := by rw [integral_const_mul]
  have hre : (β ^ 2 * ((Real.pi : ℂ) *
      exteriorInverseCoeff F (2 * k - 1))).re =
      Real.pi * (β ^ 2 * exteriorInverseCoeff F (2 * k - 1)).re := by
    have heq : β ^ 2 * ((Real.pi : ℂ) *
        exteriorInverseCoeff F (2 * k - 1)) =
        (Real.pi : ℂ) *
          (β ^ 2 * exteriorInverseCoeff F (2 * k - 1)) := by ring
    rw [heq, Complex.mul_re]
    simp
  calc
    (Real.pi : ℝ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          (β ^ 2 * actualHarmonic F z ^ (2 * k - 2) *
            deriv (exteriorForwardGerm F) (conj z)).re ∂volume) =
        (Real.pi : ℝ)⁻¹ *
          (∫ z in Metric.ball (0 : ℂ) 1,
            (β ^ 2 * G z).re ∂volume) := by
              congr 1
              apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
              intro z hz
              dsimp only [G]
              ring
    _ = (β ^ 2 * exteriorInverseCoeff F (2 * k - 1)).re := by
      rw [hReal, hBG, hre]
      field_simp [Real.pi_ne_zero]

/-- The weighted derivative energy is exactly the difference between the
actual filling moment and the actual omitted-set area moment. -/
theorem actualHarmonic_deriv_weighted_eq_moment_sub
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {k : ℕ} (hk : 1 ≤ k) :
    (Real.pi : ℝ)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖actualHarmonic F z‖ ^ (2 * k - 2) *
          ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2 ∂volume) =
      actualHarmonicMoment F (2 * k - 2) -
        actualOmittedMoment F (2 * k - 2) := by
  let m : ℕ := 2 * k - 2
  let I : ℝ := ∫ z in Metric.ball (0 : ℂ) 1,
    ‖actualHarmonic F z‖ ^ m ∂volume
  let J : ℝ := ∫ z in Metric.ball (0 : ℂ) 1,
    ‖actualHarmonic F z‖ ^ m *
      ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2 ∂volume
  let K : ℝ := ∫ w in exteriorOmitted F, ‖w‖ ^ m ∂volume
  obtain ⟨hIInt, hJInt⟩ := actualHarmonic_weighted_integrableOn F hc m
  have hsplit :
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖actualHarmonic F z‖ ^ m *
          (1 - ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2)
          ∂volume) = I - J := by
    have hpoint :
        (∫ z in Metric.ball (0 : ℂ) 1,
          ‖actualHarmonic F z‖ ^ m *
            (1 - ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2)
            ∂volume) =
        ∫ z in Metric.ball (0 : ℂ) 1,
          ‖actualHarmonic F z‖ ^ m -
            ‖actualHarmonic F z‖ ^ m *
              ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2
            ∂volume := by
      apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      intro z hz
      ring
    rw [hpoint]
    exact integral_sub hIInt hJInt
  have harea : (Real.pi : ℝ)⁻¹ * (I - J) =
      (Real.pi : ℝ)⁻¹ * K := by
    simpa only [m, K, hsplit] using
      (actualWeightedOmittedArea_eq F hc hk)
  change (Real.pi : ℝ)⁻¹ * J =
    (Real.pi : ℝ)⁻¹ * I - (Real.pi : ℝ)⁻¹ * K
  calc
    (Real.pi : ℝ)⁻¹ * J =
        (Real.pi : ℝ)⁻¹ * I - (Real.pi : ℝ)⁻¹ * (I - J) := by ring
    _ = (Real.pi : ℝ)⁻¹ * I - (Real.pi : ℝ)⁻¹ * K := by rw [harea]

/-- The full actual real-gradient energy formula with an arbitrary unit
phase. It is independent of how the phase is chosen. -/
theorem actualHarmonicPhaseEnergy_eq_moments
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {k : ℕ} (hk : 1 ≤ k) (β : ℂ) (hβ : ‖β‖ = 1) :
    actualHarmonicPhaseEnergy F k β =
      (k : ℝ) ^ 2 *
        (2 * actualHarmonicMoment F (2 * k - 2) -
          actualOmittedMoment F (2 * k - 2)) -
      2 * (k : ℝ) ^ 2 *
        (β ^ 2 * exteriorInverseCoeff F (2 * k - 1)).re := by
  have h := actualHarmonicPhaseEnergy_eq_integrals F hc hk β hβ
  have hJ := actualHarmonic_deriv_weighted_eq_moment_sub F hc hk
  have hC := actualHarmonic_phase_cross_eq_inverseCoeff F hc hk β
  rw [← actualHarmonicMoment, hJ] at h
  have hcross :
      2 * (k : ℝ) ^ 2 * (Real.pi : ℝ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          (β ^ 2 * actualHarmonic F z ^ (2 * k - 2) *
            deriv (exteriorForwardGerm F) (conj z)).re ∂volume) =
      2 * (k : ℝ) ^ 2 *
        (β ^ 2 * exteriorInverseCoeff F (2 * k - 1)).re := by
    calc
      _ = 2 * (k : ℝ) ^ 2 *
          ((Real.pi : ℝ)⁻¹ *
            (∫ z in Metric.ball (0 : ℂ) 1,
              (β ^ 2 * actualHarmonic F z ^ (2 * k - 2) *
                deriv (exteriorForwardGerm F) (conj z)).re ∂volume)) := by ring
      _ = _ := by rw [hC]
  rw [hcross] at h
  nlinarith [h]

/-- A unit phase whose square rotates a complex number onto the positive
real axis. The zero case uses the phase `1`. -/
theorem exists_unit_phase_align (B : ℂ) :
    ∃ β : ℂ, ‖β‖ = 1 ∧ (β ^ 2 * B).re = ‖B‖ := by
  by_cases hB : B = 0
  · refine ⟨1, by simp, ?_⟩
    simp [hB]
  · have hBnorm : 0 < ‖B‖ := norm_pos_iff.mpr hB
    let η : ℂ := conj B / (‖B‖ : ℂ)
    have hηnorm : ‖η‖ = 1 := by
      dsimp only [η]
      rw [norm_div, Complex.norm_conj]
      norm_cast
      rw [Real.norm_eq_abs, abs_of_pos hBnorm]
      exact div_self (ne_of_gt hBnorm)
    obtain ⟨β, hβ2⟩ :=
      IsAlgClosed.exists_pow_nat_eq η (by norm_num : 0 < 2)
    have hβnorm : ‖β‖ = 1 := by
      have hnorm := congrArg norm hβ2
      rw [norm_pow, hηnorm] at hnorm
      nlinarith [norm_nonneg β]
    refine ⟨β, hβnorm, ?_⟩
    have hBnormC : (‖B‖ : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hBnorm)
    have hprod : β ^ 2 * B = (‖B‖ : ℂ) := by
      rw [hβ2]
      dsimp only [η]
      calc
        (conj B / (‖B‖ : ℂ)) * B =
            (conj B * B) / (‖B‖ : ℂ) := by ring
        _ = ((‖B‖ : ℂ) ^ 2) / (‖B‖ : ℂ) := by
          rw [RCLike.conj_mul]
          congr 1
        _ = (‖B‖ : ℂ) := by
          field_simp [hBnormC]
    rw [hprod]
    simp

/-- Lemma 3.1's actual Dirichlet identity. The chosen phase is a unit complex
number and the energy is the integral of the squared real gradient of
`Im (β * H^k)`. The case `B_{2k-1}=0` is included. -/
theorem exists_actualHarmonicPhaseEnergy_identity
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ β : ℂ, ‖β‖ = 1 ∧
      actualHarmonicMoment F (2 * k - 2) -
        ‖exteriorInverseCoeff F (2 * k - 1)‖ =
      actualOmittedMoment F (2 * k - 2) / 2 +
        actualHarmonicPhaseEnergy F k β / (2 * (k : ℝ) ^ 2) := by
  obtain ⟨β, hβ, halign⟩ :=
    exists_unit_phase_align (exteriorInverseCoeff F (2 * k - 1))
  refine ⟨β, hβ, ?_⟩
  have hE := actualHarmonicPhaseEnergy_eq_moments F hc hk β hβ
  rw [halign] at hE
  have hkR : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hden : 2 * (k : ℝ) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ hkR)
  have hE2 : actualHarmonicPhaseEnergy F k β =
      (2 * (k : ℝ) ^ 2) *
        (actualHarmonicMoment F (2 * k - 2) -
          ‖exteriorInverseCoeff F (2 * k - 1)‖ -
          actualOmittedMoment F (2 * k - 2) / 2) := by
    rw [hE]
    ring
  rw [hE2]
  field_simp [hden]
  ring

end SpringerLean
