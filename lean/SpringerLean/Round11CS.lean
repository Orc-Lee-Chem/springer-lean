import SpringerLean.Round11GeneralSecond
import SpringerLean.Round08General

open MeasureTheory Filter
open scoped Topology ComplexConjugate ENNReal

namespace SpringerLean

/-- Complex Cauchy--Schwarz on the actual unit disk, in ordinary integral form. -/
theorem disk_complex_integral_mul_norm_sq_le
    (f g : ℂ → ℂ)
    (hf : ContinuousOn f (Metric.ball (0 : ℂ) 1))
    (hg : ContinuousOn g (Metric.ball (0 : ℂ) 1))
    (hfSq : IntegrableOn (fun z : ℂ => ‖f z‖ ^ 2)
      (Metric.ball (0 : ℂ) 1))
    (hgSq : IntegrableOn (fun z : ℂ => ‖g z‖ ^ 2)
      (Metric.ball (0 : ℂ) 1)) :
    ‖∫ z in Metric.ball (0 : ℂ) 1, f z * g z ∂volume‖ ^ 2 ≤
      (∫ z in Metric.ball (0 : ℂ) 1, ‖f z‖ ^ 2 ∂volume) *
      (∫ z in Metric.ball (0 : ℂ) 1, ‖g z‖ ^ 2 ∂volume) := by
  have hnorm :
      ‖∫ z in Metric.ball (0 : ℂ) 1, f z * g z ∂volume‖ ≤
        ∫ z in Metric.ball (0 : ℂ) 1, ‖f z‖ * ‖g z‖ ∂volume := by
    simpa only [norm_mul] using
      (norm_integral_le_integral_norm
        (f := fun z : ℂ => f z * g z)
        (μ := volume.restrict (Metric.ball (0 : ℂ) 1)))
  have hcs := disk_integral_norm_mul_le_sqrt_sq f g hf hg hfSq hgSq
  have hleft := hnorm.trans hcs
  have ha : 0 ≤ ∫ z in Metric.ball (0 : ℂ) 1, ‖f z‖ ^ 2 ∂volume :=
    integral_nonneg (fun z => sq_nonneg _)
  have hb : 0 ≤ ∫ z in Metric.ball (0 : ℂ) 1, ‖g z‖ ^ 2 ∂volume :=
    integral_nonneg (fun z => sq_nonneg _)
  have hsqa := Real.sq_sqrt ha
  have hsqb := Real.sq_sqrt hb
  have hroot : 0 ≤
      Real.sqrt (∫ z in Metric.ball (0 : ℂ) 1, ‖f z‖ ^ 2 ∂volume) *
        Real.sqrt (∫ z in Metric.ball (0 : ℂ) 1, ‖g z‖ ^ 2 ∂volume) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmul := mul_nonneg (sub_nonneg.mpr hleft)
    (add_nonneg hroot
      (norm_nonneg (∫ z in Metric.ball (0 : ℂ) 1,
        f z * g z ∂volume)))
  calc
    ‖∫ z in Metric.ball (0 : ℂ) 1, f z * g z ∂volume‖ ^ 2 ≤
        (Real.sqrt (∫ z in Metric.ball (0 : ℂ) 1,
          ‖f z‖ ^ 2 ∂volume) *
          Real.sqrt (∫ z in Metric.ball (0 : ℂ) 1,
            ‖g z‖ ^ 2 ∂volume)) ^ 2 := by nlinarith
    _ = (∫ z in Metric.ball (0 : ℂ) 1, ‖f z‖ ^ 2 ∂volume) *
        (∫ z in Metric.ball (0 : ℂ) 1, ‖g z‖ ^ 2 ∂volume) := by
          rw [mul_pow, hsqa, hsqb]

/-- The actual harmonic filling and the actual derivative satisfy the
weighted disk Cauchy--Schwarz estimate in every even order. -/
theorem actualHarmonic_weighted_disk_cauchy_schwarz
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (p : ℕ) :
    ‖∫ z in Metric.ball (0 : ℂ) 1,
      (actualHarmonic F z) ^ (2 * p) *
        deriv (exteriorForwardGerm F) (conj z) ∂volume‖ ^ 2 ≤
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖actualHarmonic F z‖ ^ (2 * p) ∂volume) *
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖actualHarmonic F z‖ ^ (2 * p) *
          ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2 ∂volume) := by
  let D : Set ℂ := Metric.ball 0 1
  let H : ℂ → ℂ := actualHarmonic F
  let d : ℂ → ℂ := fun z => deriv (exteriorForwardGerm F) (conj z)
  let f : ℂ → ℂ := fun z => H z ^ p
  let g : ℂ → ℂ := fun z => H z ^ p * d z
  have hvol : volume D ≠ ∞ := by
    rw [Complex.volume_ball]
    finiteness
  haveI : IsFiniteMeasure (volume.restrict D) :=
    isFiniteMeasure_restrict.mpr hvol
  obtain ⟨C, hC0, hC⟩ := exteriorForwardGerm_bounded_unitDisk F hc
  have hHcont : ContinuousOn H D := actualHarmonic_continuousOn_unitBall F hc
  have hdcont : ContinuousOn d D :=
    exteriorForwardGerm_deriv_conj_continuousOn_unitBall F hc
  have hbound : ∀ z ∈ D, ‖H z‖ ≤ 1 + C := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by
      simpa only [D, Metric.mem_ball, dist_zero_right] using hz
    have hcz : ‖conj z‖ < 1 := by
      simpa only [Complex.norm_conj] using hz1
    dsimp only [H, actualHarmonic]
    calc
      ‖z + exteriorForwardGerm F (conj z)‖ ≤
          ‖z‖ + ‖exteriorForwardGerm F (conj z)‖ := norm_add_le _ _
      _ ≤ 1 + C := by linarith [hC (conj z) hcz]
  have hC1 : 0 ≤ 1 + C := by linarith
  have hwcont : ContinuousOn (fun z : ℂ => ‖H z‖ ^ (2 * p)) D :=
    hHcont.norm.pow _
  have hwbound : ∀ z ∈ D, |‖H z‖ ^ (2 * p)| ≤ (1 + C) ^ (2 * p) := by
    intro z hz
    rw [abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound z hz) _
  have hwi : IntegrableOn (fun z : ℂ => ‖H z‖ ^ (2 * p)) D := by
    have h := disk_integrable_bounded_weight_mul
      (fun z : ℂ => ‖H z‖ ^ (2 * p)) (fun _ => (1 : ℝ))
      ((1 + C) ^ (2 * p)) (pow_nonneg hC1 _)
      hwcont (integrable_const _) hwbound
    simpa only [mul_one] using h
  have hdSq : IntegrableOn (fun z : ℂ => ‖d z‖ ^ 2) D :=
    (exteriorForwardGerm_deriv_sq_integrable_le_one F hc).1
  have hwdSq : IntegrableOn
      (fun z : ℂ => ‖H z‖ ^ (2 * p) * ‖d z‖ ^ 2) D :=
    disk_integrable_bounded_weight_mul
      (fun z : ℂ => ‖H z‖ ^ (2 * p))
      (fun z : ℂ => ‖d z‖ ^ 2)
      ((1 + C) ^ (2 * p)) (pow_nonneg hC1 _)
      hwcont hdSq hwbound
  have hfcont : ContinuousOn f D := hHcont.pow _
  have hgcont : ContinuousOn g D := hfcont.mul hdcont
  have hfSq : IntegrableOn (fun z : ℂ => ‖f z‖ ^ 2) D := by
    change IntegrableOn (fun z => ‖H z ^ p‖ ^ 2) D
    simpa only [norm_pow, ← pow_mul, show p * 2 = 2 * p by omega] using hwi
  have hgSq : IntegrableOn (fun z : ℂ => ‖g z‖ ^ 2) D := by
    change IntegrableOn (fun z => ‖H z ^ p * d z‖ ^ 2) D
    simpa only [norm_mul, mul_pow, norm_pow, ← pow_mul,
      show p * 2 = 2 * p by omega] using hwdSq
  have hcs := disk_complex_integral_mul_norm_sq_le
    f g hfcont hgcont hfSq hgSq
  have hfg : ∀ z, f z * g z = H z ^ (2 * p) * d z := by
    intro z
    dsimp only [f, g]
    rw [← mul_assoc, ← pow_add, show p + p = 2 * p by omega]
  have hfn : ∀ z, ‖f z‖ ^ 2 = ‖H z‖ ^ (2 * p) := by
    intro z
    dsimp only [f]
    rw [norm_pow, ← pow_mul, show p * 2 = 2 * p by omega]
  have hgn : ∀ z, ‖g z‖ ^ 2 = ‖H z‖ ^ (2 * p) * ‖d z‖ ^ 2 := by
    intro z
    dsimp only [g]
    rw [norm_mul, mul_pow, norm_pow, ← pow_mul,
      show p * 2 = 2 * p by omega]
  simp_rw [hfg, hfn, hgn] at hcs
  exact hcs

/-- Integrability of the two weighted quantities appearing in the area
identity and in the Cauchy--Schwarz estimate. -/
theorem actualHarmonic_weighted_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (m : ℕ) :
    IntegrableOn (fun z : ℂ => ‖actualHarmonic F z‖ ^ m)
      (Metric.ball (0 : ℂ) 1) ∧
    IntegrableOn (fun z : ℂ => ‖actualHarmonic F z‖ ^ m *
      ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2)
      (Metric.ball (0 : ℂ) 1) := by
  let D : Set ℂ := Metric.ball 0 1
  let H : ℂ → ℂ := actualHarmonic F
  let d : ℂ → ℂ := fun z => deriv (exteriorForwardGerm F) (conj z)
  obtain ⟨C, hC0, hC⟩ := exteriorForwardGerm_bounded_unitDisk F hc
  have hvol : volume D ≠ ∞ := by
    rw [Complex.volume_ball]
    finiteness
  haveI : IsFiniteMeasure (volume.restrict D) :=
    isFiniteMeasure_restrict.mpr hvol
  have hHcont : ContinuousOn H D := actualHarmonic_continuousOn_unitBall F hc
  have hbound : ∀ z ∈ D, ‖H z‖ ≤ 1 + C := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by
      simpa only [D, Metric.mem_ball, dist_zero_right] using hz
    have hcz : ‖conj z‖ < 1 := by
      simpa only [Complex.norm_conj] using hz1
    dsimp only [H, actualHarmonic]
    calc
      ‖z + exteriorForwardGerm F (conj z)‖ ≤
          ‖z‖ + ‖exteriorForwardGerm F (conj z)‖ := norm_add_le _ _
      _ ≤ 1 + C := by linarith [hC (conj z) hcz]
  have hC1 : 0 ≤ 1 + C := by linarith
  have hwcont : ContinuousOn (fun z : ℂ => ‖H z‖ ^ m) D :=
    hHcont.norm.pow _
  have hwbound : ∀ z ∈ D, |‖H z‖ ^ m| ≤ (1 + C) ^ m := by
    intro z hz
    rw [abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound z hz) _
  have hdSq : IntegrableOn (fun z : ℂ => ‖d z‖ ^ 2) D :=
    (exteriorForwardGerm_deriv_sq_integrable_le_one F hc).1
  constructor
  · have h := disk_integrable_bounded_weight_mul
      (fun z : ℂ => ‖H z‖ ^ m) (fun _ => (1 : ℝ))
      ((1 + C) ^ m) (pow_nonneg hC1 _)
      hwcont (integrable_const _) hwbound
    simpa only [mul_one, D, H] using h
  · exact disk_integrable_bounded_weight_mul
      (fun z : ℂ => ‖H z‖ ^ m)
      (fun z : ℂ => ‖d z‖ ^ 2)
      ((1 + C) ^ m) (pow_nonneg hC1 _)
      hwcont hdSq hwbound

/-- The normalized `m`th moment of the actual harmonic filling. -/
noncomputable def actualHarmonicMoment (F : ℂ → ℂ) (m : ℕ) : ℝ :=
  (Real.pi : ℝ)⁻¹ *
    (∫ z in Metric.ball (0 : ℂ) 1,
      ‖actualHarmonic F z‖ ^ m ∂volume)

/-- The normalized `m`th area moment of the actual omitted set. -/
noncomputable def actualOmittedMoment (F : ℂ → ℂ) (m : ℕ) : ℝ :=
  (Real.pi : ℝ)⁻¹ *
    (∫ w in exteriorOmitted F, ‖w‖ ^ m ∂volume)

/-- Lemma 3.1's Cauchy--Schwarz consequence for the original exterior map,
with no regularity or area assumption added to the paper's function class. -/
theorem exteriorInverseCoeff_odd_norm_sq_le_moment_product
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {k : ℕ} (hk : 1 ≤ k) :
    ‖exteriorInverseCoeff F (2 * k - 1)‖ ^ 2 ≤
      actualHarmonicMoment F (2 * k - 2) *
        (actualHarmonicMoment F (2 * k - 2) -
          actualOmittedMoment F (2 * k - 2)) := by
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
  have harea : I - J = K := by
    have h := actualWeightedOmittedArea_eq F hc hk
    have hpi : (Real.pi : ℝ)⁻¹ ≠ 0 :=
      inv_ne_zero Real.pi_ne_zero
    have heq : (Real.pi : ℝ)⁻¹ * (I - J) =
        (Real.pi : ℝ)⁻¹ * K := by
      simpa only [m, K, hsplit] using h
    exact mul_left_cancel₀ hpi heq
  have hp : 2 * (k - 1) = m := by
    dsimp only [m]
    omega
  have hcs :
      ‖∫ z in Metric.ball (0 : ℂ) 1,
        actualHarmonic F z ^ m *
          deriv (exteriorForwardGerm F) (conj z) ∂volume‖ ^ 2 ≤
      I * J := by
    simpa only [hp, I, J] using
      (actualHarmonic_weighted_disk_cauchy_schwarz F hc (k - 1))
  have hB : exteriorInverseCoeff F (2 * k - 1) =
      (Real.pi : ℂ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          actualHarmonic F z ^ m *
            deriv (exteriorForwardGerm F) (conj z) ∂volume) := by
    simpa only [m, actualHarmonic] using
      (exteriorInverseCoeff_odd_eq_actualHarmonic_diskIntegral F hc hk)
  have hpinorm : ‖(Real.pi : ℂ)⁻¹‖ = (Real.pi : ℝ)⁻¹ := by
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hnorm : ‖exteriorInverseCoeff F (2 * k - 1)‖ ^ 2 ≤
      (Real.pi : ℝ)⁻¹ ^ 2 * (I * J) := by
    rw [hB, norm_mul, hpinorm, mul_pow]
    exact mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
  have hMJ :
      (Real.pi : ℝ)⁻¹ * I *
        ((Real.pi : ℝ)⁻¹ * I - (Real.pi : ℝ)⁻¹ * K) =
      (Real.pi : ℝ)⁻¹ ^ 2 * (I * J) := by
    rw [← harea]
    ring
  simpa only [actualHarmonicMoment, actualOmittedMoment, m, I, K,
    ← hMJ] using hnorm

end SpringerLean
