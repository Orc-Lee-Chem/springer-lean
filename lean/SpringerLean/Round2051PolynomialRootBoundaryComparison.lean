import SpringerLean.Round2049ExteriorLogMomentComparison
import SpringerLean.Round2050LogHingePower
import SpringerLean.Round1860ActualRealMomentLimit
import SpringerLean.Round1982ConditionalZeroUpper

open Real Set MeasureTheory Polynomial Filter
open scoped Topology

namespace SpringerLean

private theorem integral_radialLogHingeWeight_fubini
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    (f : α → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (p : ℝ) (hp : 0 < p) (hint : Integrable (fun x => f x ^ p) μ) :
    Integrable (fun t : ℝ => ∫ x, radialLogHingeWeight p (f x) t ∂μ) ∧
      (∫ t : ℝ, ∫ x, radialLogHingeWeight p (f x) t ∂μ) =
        (∫ x, f x ^ p ∂μ) / p ^ 2 := by
  let K (x : α) (t : ℝ) := radialLogHingeWeight p (f x) t
  have hm : Measurable (Function.uncurry K) := by
    change Measurable (fun z : α × ℝ => radialLogHingeWeight p (f z.1) z.2)
    unfold radialLogHingeWeight
    fun_prop
  have hintK : Integrable (Function.uncurry K) (μ.prod volume) := by
    refine (integrable_prod_iff hm.aestronglyMeasurable).2 ⟨.of_forall fun x =>
      (radialLogHingeWeight_integral p (f x) hp (hf0 x)).1, ?_⟩
    have heq (x : α) :
        (∫ t, ‖K x t‖) = f x ^ p / p ^ 2 := by
      calc
        _ = ∫ t, radialLogHingeWeight p (f x) t := by
          apply integral_congr_ae
          exact .of_forall fun t => norm_of_nonneg (radialLogHingeWeight_nonneg p (f x) t)
        _ = _ := (radialLogHingeWeight_integral p (f x) hp (hf0 x)).2
    simpa only [Function.uncurry_apply_pair, heq] using hint.div_const (p ^ 2)
  refine ⟨hintK.integral_prod_right, ?_⟩
  change (∫ t : ℝ, ∫ x, K x t ∂μ) = _
  rw [← integral_integral_swap hintK]
  simp_rw [K, fun x => (radialLogHingeWeight_integral p (f x) hp (hf0 x)).2]
  exact integral_div _ _

private theorem integral_radialLogHingeWeight_multiset
    (s : Multiset ℂ) (p : ℝ) (hp : 0 < p) :
    Integrable (fun t : ℝ => (s.map (fun z => radialLogHingeWeight p ‖z‖ t)).sum) ∧
      (∫ t : ℝ, (s.map (fun z => radialLogHingeWeight p ‖z‖ t)).sum) =
        (s.map (fun z => ‖z‖ ^ p)).sum / p ^ 2 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    obtain ⟨hA, hB⟩ := radialLogHingeWeight_integral p ‖z‖ hp (norm_nonneg z)
    simp only [Multiset.map_cons, Multiset.sum_cons]
    refine ⟨hA.add ih.1, ?_⟩
    rw [integral_add hA ih.1, hB, ih.2, add_div]

/-- Root means are controlled by every smooth exterior circle, for
every positive exponent. The proof integrates the logarithmic hinge
comparison and works with the actual multiplicity-counted roots. -/
theorem polynomial_root_power_mean_le_exterior_circle
    (Q : ℂ[X]) (hQ : Q.Monic) (hdeg : 0 < Q.natDegree)
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hidentity : ∀ w ∈ exteriorDisk, Q.eval (F w) = w ^ Q.natDegree)
    (p : ℝ) (hp : 0 < p) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (Q.roots.map (fun z : ℂ => ‖z‖ ^ p)).sum / (Q.natDegree : ℝ) ≤
      circleAverage (fun z => ‖F z‖ ^ p) 0 r⁻¹ := by
  let J := Ioc (0 : ℝ) (2 * π)
  let μ : Measure ℝ := volume.restrict J
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    dsimp [J]
    rw [Real.volume_Ioc]
    finiteness)
  let f : ℝ → ℝ := fun θ => ‖F (circleMap 0 r⁻¹ θ)‖
  have hmem (θ : ℝ) : circleMap 0 r⁻¹ θ ∈ exteriorDisk := by
    change 1 < ‖circleMap 0 r⁻¹ θ‖
    simp only [norm_circleMap_zero, abs_of_pos (inv_pos.mpr hr)]
    exact (one_lt_inv₀ hr).mpr hr1
  have hf : Continuous f :=
    (hF.1.continuousOn.comp_continuous (continuous_circleMap _ _) hmem).norm
  have hfp : Integrable (fun θ => f θ ^ p) μ := by
    have hcont := (Real.continuous_rpow_const hp.le).comp hf
    exact (hcont.continuousOn.integrableOn_compact (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π))).mono_set
      Ioc_subset_Icc_self
  obtain ⟨hleftInt, hleftEq⟩ := integral_radialLogHingeWeight_multiset Q.roots p hp
  obtain ⟨hrightInt, hrightEq⟩ := integral_radialLogHingeWeight_fubini f hf.measurable
    (fun θ => norm_nonneg _) p hp hfp
  have hmono (t : ℝ) :
      (Q.roots.map (fun z : ℂ => radialLogHingeWeight p ‖z‖ t)).sum /
        (Q.natDegree : ℝ) ≤
        (2 * π)⁻¹ * (∫ θ, radialLogHingeWeight p (f θ) t ∂μ) := by
    have hh := polynomial_root_posLog_mean_le_exterior_circle Q hQ hdeg F hF
      hidentity r hr hr1 (Real.exp t) (Real.exp_pos t)
    have hsum (s : Multiset ℂ) :
        (s.map (fun z : ℂ => radialLogHingeWeight p ‖z‖ t)).sum =
          Real.exp (p * t) * (s.map (fun z : ℂ => Real.posLog (‖z‖ / Real.exp t))).sum := by
      induction s using Multiset.induction_on with
      | empty => simp
      | cons a s ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons]
        rw [ih, radialLogHingeWeight, mul_add]
    rw [hsum]
    have hh' := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg (p * t))
    simpa only [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le two_pi_pos.le,
      radialLogHingeWeight, μ, J, f, integral_const_mul, mul_div_assoc, mul_left_comm] using hh'
  have h := integral_mono (hleftInt.div_const (Q.natDegree : ℝ))
    (hrightInt.const_mul (2 * π)⁻¹) hmono
  rw [integral_div, integral_const_mul, hleftEq, hrightEq] at h
  have h2 : (Q.roots.map (fun z : ℂ => ‖z‖ ^ p)).sum / (Q.natDegree : ℝ) ≤
      (2 * π)⁻¹ * (∫ θ, f θ ^ p ∂μ) := by
    apply (div_le_div_iff_of_pos_right (pow_pos hp 2)).mp
    convert h using 1
    · ring
    · ring
  simpa only [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le two_pi_pos.le,
    μ, J, f] using h2

/-- The root-to-boundary comparison for the actual radial trace.
The exterior identity is supplied by the lemniscate exterior map. -/
theorem polynomial_root_power_mean_le_actual_radial
    (Q : ℂ[X]) (hQ : Q.Monic) (hdeg : 0 < Q.natDegree)
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hidentity : ∀ w ∈ exteriorDisk, Q.eval (F w) = w ^ Q.natDegree)
    (p : ℝ) (hp : 0 < p) :
    (Q.roots.map (fun z : ℂ => ‖z‖ ^ p)).sum / (Q.natDegree : ℝ) ≤
      actualBoundaryRadialMoment F p := by
  apply ge_of_tendsto (actualBoundaryRadialMoment_circle_tendsto F hF p hp.le)
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
  exact polynomial_root_power_mean_le_exterior_circle Q hQ hdeg F hF hidentity p hp r hr.1 hr.2

/-- The strict original-zero bound, from the normalized exterior
identity alone. The construction of the exterior map remains separate. -/
theorem polynomial_root_power_mean_strict_of_exterior_identity
    (Q : ℂ[X]) (hQ : Q.Monic) (hdeg : 0 < Q.natDegree)
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hidentity : ∀ w ∈ exteriorDisk, Q.eval (F w) = w ^ Q.natDegree)
    (p : ℝ) (hp4 : 4 ≤ p) (hp8 : p ≤ 8) :
    (Q.roots.map (fun z : ℂ => ‖z‖ ^ p)).sum / (Q.natDegree : ℝ) <
      slitRadialMomentConstant p := by
  have h := polynomial_root_power_mean_le_actual_radial Q hQ hdeg F hF hidentity
    p (by linarith)
  simpa only [Function.iterate_zero, id_eq, Nat.sub_zero] using
    polynomial_derivative_zero_moment_strict_of_analytic_comparisons
      Q hQ hdeg F hF hidentity 0 hdeg p hp4 hp8 (by simp) h

end SpringerLean
