import SpringerLean.Round1919CosineMomentBound

open MeasureTheory Set
open scoped ComplexConjugate

namespace SpringerLean

set_option maxHeartbeats 30000

private theorem normalized_trace_power_integrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun t : ℝ =>
      (‖actualExteriorRadialTrace F t‖ / 2) ^ q)
      (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
  have hpoint (t : ℝ) :
      (‖actualExteriorRadialTrace F t‖ / 2) ^ q =
        ‖actualExteriorRadialTrace F t‖ ^ q / (2 : ℝ) ^ q := by
    rw [Real.div_rpow (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  simp_rw [hpoint]
  exact (actualBoundaryRadialMoment_integrable F hc q hq).div_const _

private theorem normalized_projection_square_integrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    (hcunit : ‖c‖ = 1) :
    Integrable (fun t : ℝ =>
      ((c * actualExteriorRadialTrace F t).re / 2) ^ 2)
      (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
  let μ : Measure ℝ := volume.restrict (Ioo (-Real.pi) Real.pi)
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    rw [Real.volume_Ioo]
    finiteness)
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => ((c * actualExteriorRadialTrace F t).re / 2) ^ 2) μ := by
    have hcont : Continuous (fun z : ℂ => ((c * z).re / 2) ^ 2) := by
      fun_prop
    exact hcont.comp_aestronglyMeasurable
      (actualExteriorRadialTrace_aestronglyMeasurable F hc)
  apply (integrable_const (1 : ℝ)).mono' hmeas
  filter_upwards [actualExteriorRadialTrace_ae_norm_le_two F hc] with t ht
  have hre : |(c * actualExteriorRadialTrace F t).re / 2| ≤ 1 := by
    calc
      _ = |(c * actualExteriorRadialTrace F t).re| / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ ‖c * actualExteriorRadialTrace F t‖ / 2 :=
        div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (by norm_num)
      _ ≤ 1 := by rw [norm_mul, hcunit, one_mul]; linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rcases abs_le.mp hre with ⟨hlo, hhi⟩
  nlinarith

private theorem normalized_cosine_power_circleIntegrable
    (q : ℝ) (hq : 0 ≤ q) :
    CircleIntegrable (fun z : ℂ => |z.re| ^ q) 0 1 := by
  have h : Continuous (fun z : ℂ => |z.re| ^ q) := by
    have hr := Real.continuous_rpow_const hq
    fun_prop
  exact h.continuousOn.circleIntegrable (by norm_num)

/-- Integral expansion of the compensated test for one actual map. The
endpoint deficits and first-mode correction can now be inserted directly. -/
theorem actual_interpolation_deficit_from_test
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (c : ℂ) (hcunit : ‖c‖ = 1)
    {a θ : ℝ} (ha : 4 ≤ a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let p := a + 2 * θ
    let κ := p * θ * (1 - θ) * interpolationCurvatureConstant a
    (p * (1 - θ) / a) *
        (normalizedCosineMoment a - normalizedActualRadialMoment F a) +
      (p * θ / (a + 2)) *
        (normalizedCosineMoment (a + 2) -
          normalizedActualRadialMoment F (a + 2)) -
      κ * (1 / 2 - actualBoundaryProjectionSecondMoment F c) ≤
        normalizedCosineMoment p - normalizedActualRadialMoment F p := by
  let p := a + 2 * θ
  let κ := p * θ * (1 - θ) * interpolationCurvatureConstant a
  let μ : Measure ℝ := volume.restrict (Ioo (-Real.pi) Real.pi)
  let T : ℝ → ℝ := fun t => ‖actualExteriorRadialTrace F t‖ / 2
  let X : ℝ → ℝ := fun t => (c * actualExteriorRadialTrace F t).re / 2
  let k₁ := p * (1 - θ) / a
  let k₂ := p * θ / (a + 2)
  let h := interpolationPowerTest a θ
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have ha0 : 0 ≤ a := by linarith
  have ha2 : 0 ≤ a + 2 := by linarith
  have hTp := normalized_trace_power_integrable F hc p hp
  have hTa := normalized_trace_power_integrable F hc a ha0
  have hTb := normalized_trace_power_integrable F hc (a + 2) ha2
  have hXi := normalized_projection_square_integrable F hc c hcunit
  have htransfer := actualRadialTrace_interpolation_test_le_cosine
    F hc (conj c) (by simpa only [Complex.norm_conj] using hcunit)
    ha hθ0 hθ1
  simp only [Complex.conj_conj] at htransfer
  have hleft :
      (2 * Real.pi)⁻¹ *
        (∫ t in Ioo (-Real.pi) Real.pi,
          h (T t) + κ * (X t) ^ 2) =
      normalizedActualRadialMoment F p -
        k₁ * normalizedActualRadialMoment F a -
        k₂ * normalizedActualRadialMoment F (a + 2) +
        κ * actualBoundaryProjectionSecondMoment F c := by
    have hform (t : ℝ) : h (T t) + κ * (X t) ^ 2 =
        ((T t) ^ p - k₁ * (T t) ^ a - k₂ * (T t) ^ (a + 2)) +
          κ * (X t) ^ 2 := by
      rfl
    have hsub : Integrable (fun t => (T t) ^ p - k₁ * (T t) ^ a) μ :=
      hTp.sub (hTa.const_mul k₁)
    have hsub2 : Integrable
        (fun t => (T t) ^ p - k₁ * (T t) ^ a - k₂ * (T t) ^ (a + 2)) μ :=
      hsub.sub (hTb.const_mul k₂)
    have hMp : (2 * Real.pi)⁻¹ *
        (∫ t in Ioo (-Real.pi) Real.pi, (T t) ^ p) =
          normalizedActualRadialMoment F p := by
      simpa only [T] using (normalizedActualRadialMoment_eq_integral F p).symm
    have hMa : (2 * Real.pi)⁻¹ *
        (∫ t in Ioo (-Real.pi) Real.pi, (T t) ^ a) =
          normalizedActualRadialMoment F a := by
      simpa only [T] using (normalizedActualRadialMoment_eq_integral F a).symm
    have hMb : (2 * Real.pi)⁻¹ *
        (∫ t in Ioo (-Real.pi) Real.pi, (T t) ^ (a + 2)) =
          normalizedActualRadialMoment F (a + 2) := by
      simpa only [T] using
        (normalizedActualRadialMoment_eq_integral F (a + 2)).symm
    have hEX : (2 * Real.pi)⁻¹ *
        (∫ t in Ioo (-Real.pi) Real.pi, (X t) ^ 2) =
          actualBoundaryProjectionSecondMoment F c := by
      rfl
    simp_rw [hform]
    rw [integral_add hsub2 (hXi.const_mul κ),
      integral_sub hsub (hTb.const_mul k₂),
      integral_sub hTp (hTa.const_mul k₁)]
    simp only [integral_const_mul]
    calc
      _ = ((2 * Real.pi)⁻¹ *
            ∫ t in Ioo (-Real.pi) Real.pi, (T t) ^ p) -
          k₁ * ((2 * Real.pi)⁻¹ *
            ∫ t in Ioo (-Real.pi) Real.pi, (T t) ^ a) -
          k₂ * ((2 * Real.pi)⁻¹ *
            ∫ t in Ioo (-Real.pi) Real.pi, (T t) ^ (a + 2)) +
          κ * ((2 * Real.pi)⁻¹ *
            ∫ t in Ioo (-Real.pi) Real.pi, (X t) ^ 2) := by ring
      _ = _ := by rw [hMp, hMa, hMb, hEX]
  have hright :
      Real.circleAverage
        (fun z : ℂ => h |z.re| + κ * z.re ^ 2) 0 1 =
      normalizedCosineMoment p - k₁ * normalizedCosineMoment a -
        k₂ * normalizedCosineMoment (a + 2) + κ / 2 := by
    have hCp := normalized_cosine_power_circleIntegrable p hp
    have hCa := normalized_cosine_power_circleIntegrable a ha0
    have hCb := normalized_cosine_power_circleIntegrable (a + 2) ha2
    have hC2 : Real.circleAverage (fun z : ℂ => z.re ^ 2) 0 1 = 1 / 2 := by
      have hh := normalizedCosineMoment_two
      change Real.circleAverage (fun z : ℂ => |z.re| ^ (2 : ℝ)) 0 1 = 1 / 2 at hh
      calc
        _ = Real.circleAverage (fun z : ℂ => |z.re| ^ (2 : ℝ)) 0 1 := by
          apply Real.circleAverage_congr_sphere
          intro z hz
          change z.re ^ 2 = |z.re| ^ (2 : ℝ)
          rw [Real.rpow_two, sq_abs]
        _ = 1 / 2 := hh
    have hCpc : Continuous (fun z : ℂ => |z.re| ^ p) := by
      have hh := Real.continuous_rpow_const hp
      fun_prop
    have hCac : Continuous (fun z : ℂ => |z.re| ^ a) := by
      have hh := Real.continuous_rpow_const ha0
      fun_prop
    have hCbc : Continuous (fun z : ℂ => |z.re| ^ (a + 2)) := by
      have hh := Real.continuous_rpow_const ha2
      fun_prop
    have hZc : Continuous (fun z : ℂ => z.re ^ 2) := by fun_prop
    have hsubC : CircleIntegrable
        (fun z : ℂ => |z.re| ^ p - k₁ * |z.re| ^ a) 0 1 :=
      (hCpc.sub (hCac.const_mul k₁)).continuousOn.circleIntegrable (by norm_num)
    have hsub2C : CircleIntegrable
        (fun z : ℂ => |z.re| ^ p - k₁ * |z.re| ^ a -
          k₂ * |z.re| ^ (a + 2)) 0 1 :=
      ((hCpc.sub (hCac.const_mul k₁)).sub
        (hCbc.const_mul k₂)).continuousOn.circleIntegrable (by norm_num)
    have hA : CircleIntegrable (fun z : ℂ => k₁ * |z.re| ^ a) 0 1 :=
      (hCac.const_mul k₁).continuousOn.circleIntegrable (by norm_num)
    have hB : CircleIntegrable
        (fun z : ℂ => k₂ * |z.re| ^ (a + 2)) 0 1 :=
      (hCbc.const_mul k₂).continuousOn.circleIntegrable (by norm_num)
    have hK : CircleIntegrable (fun z : ℂ => κ * z.re ^ 2) 0 1 :=
      (hZc.const_mul κ).continuousOn.circleIntegrable (by norm_num)
    have hscaleA : Real.circleAverage
        (fun z : ℂ => k₁ * |z.re| ^ a) 0 1 =
          k₁ * normalizedCosineMoment a := by
      simpa only [normalizedCosineMoment, smul_eq_mul] using
        (Real.circleAverage_fun_smul (a := k₁)
          (f := fun z : ℂ => |z.re| ^ a) (c := (0 : ℂ)) (R := 1))
    have hscaleB : Real.circleAverage
        (fun z : ℂ => k₂ * |z.re| ^ (a + 2)) 0 1 =
          k₂ * normalizedCosineMoment (a + 2) := by
      simpa only [normalizedCosineMoment, smul_eq_mul] using
        (Real.circleAverage_fun_smul (a := k₂)
          (f := fun z : ℂ => |z.re| ^ (a + 2))
          (c := (0 : ℂ)) (R := 1))
    have hscaleK : Real.circleAverage
        (fun z : ℂ => κ * z.re ^ 2) 0 1 = κ / 2 := by
      have hh := Real.circleAverage_fun_smul (a := κ)
        (f := fun z : ℂ => z.re ^ 2) (c := (0 : ℂ)) (R := 1)
      simp only [smul_eq_mul, hC2] at hh
      linarith
    have hpoint (z : ℂ) : h |z.re| + κ * z.re ^ 2 =
        (|z.re| ^ p - k₁ * |z.re| ^ a -
          k₂ * |z.re| ^ (a + 2)) + κ * z.re ^ 2 := by
      rfl
    simp_rw [hpoint]
    rw [Real.circleAverage_fun_add hsub2C hK,
      Real.circleAverage_fun_sub hsubC hB,
      Real.circleAverage_fun_sub hCp hA,
      hscaleA, hscaleB, hscaleK]
    rfl
  dsimp only [p, κ, k₁, k₂] at hleft hright ⊢
  rw [hleft, hright] at htransfer
  linarith

end SpringerLean

#print axioms SpringerLean.actual_interpolation_deficit_from_test
