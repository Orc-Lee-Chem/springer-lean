import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

open MeasureTheory ProbabilityTheory Module
open scoped RealInnerProductSpace ComplexConjugate

namespace SpringerLean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The Gaussian interaction of two finite probabilities. -/
noncomputable def gaussianInteraction (t : ℝ) (μ ν : Measure E) : ℝ :=
  ∫ p : E × E, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂μ.prod ν

private theorem gaussianPhase_sub (v x y : E) :
    Complex.exp (↑⟪x-y, v⟫ * Complex.I) =
      Complex.exp (↑⟪x, v⟫ * Complex.I) * Complex.exp (↑⟪y, -v⟫ * Complex.I) := by
  rw [← Complex.exp_add, inner_sub_left, inner_neg_right, Complex.ofReal_sub, Complex.ofReal_neg]
  congr 1
  ring

private theorem gaussianInteraction_complex (t : ℝ) (ht : 0 ≤ t)
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (gaussianInteraction t μ ν : ℂ) =
      ∫ v, charFun μ (Real.sqrt (2*t) • v) *
        conj (charFun ν (Real.sqrt (2*t) • v)) ∂stdGaussian E := by
  let c := Real.sqrt (2*t)
  let f (p : E × E) (v : E) :=
    Complex.exp (↑⟪p.1 - p.2, c • v⟫ * Complex.I)
  have hf : Integrable (Function.uncurry f) ((μ.prod ν).prod (stdGaussian E)) := by
    apply Integrable.mono (integrable_const (1 : ℝ)) (by unfold Function.uncurry f; fun_prop)
    filter_upwards with p
    simp [Function.uncurry, f, Complex.norm_exp_ofReal_mul_I]
  have hleft (p : E × E) :
      (∫ v, f p v ∂stdGaussian E) = (Real.exp (-t * ‖p.1-p.2‖^2) : ℂ) := by
    have harg (v : E) : ⟪p.1-p.2, c • v⟫ = ⟪v, c • (p.1-p.2)⟫ := by
      simp only [real_inner_smul_right]
      rw [real_inner_comm (p.1-p.2) v]
    simp_rw [f, harg]
    rw [← charFun_apply, charFun_stdGaussian, Complex.ofReal_exp]
    have hc : c ^ 2 = 2*t := Real.sq_sqrt (by positivity)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    congr 1
    have heq : -(c * ‖p.1 - p.2‖) ^ 2 / 2 = -t * ‖p.1 - p.2‖ ^ 2 := by
      rw [mul_pow, hc]
      ring
    exact_mod_cast heq
  have hright (v : E) :
      (∫ p, f p v ∂μ.prod ν) =
        charFun μ (c • v) * conj (charFun ν (c • v)) := by
    simp_rw [f, gaussianPhase_sub]
    rw [integral_prod_mul (fun x : E => Complex.exp (↑⟪x, c • v⟫ * Complex.I))
      (fun y : E => Complex.exp (↑⟪y, -(c • v)⟫ * Complex.I))]
    exact congrArg (charFun μ (c • v) * ·) (charFun_neg (μ := ν) (c • v))
  have hswap := integral_integral_swap hf
  simp_rw [hleft, hright] at hswap
  simpa only [gaussianInteraction, integral_complex_ofReal] using hswap

/-- The difference measure of two probabilities has nonnegative
Gaussian energy at every scale. This form uses ordinary positive
measures and the squared norm of the difference of their Fourier
transforms. -/
theorem gaussianInteraction_difference_eq_integral (t : ℝ) (ht : 0 ≤ t)
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    gaussianInteraction t μ μ + gaussianInteraction t ν ν -
      gaussianInteraction t μ ν - gaussianInteraction t ν μ =
      ∫ v, ‖charFun μ (Real.sqrt (2*t) • v) -
        charFun ν (Real.sqrt (2*t) • v)‖^2 ∂stdGaussian E := by
  let c := Real.sqrt (2*t)
  let γ := stdGaussian E
  let A (v : E) := charFun μ (c • v)
  let B (v : E) := charFun ν (c • v)
  have hcomplex (μ' ν' : Measure E) [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν'] :
      Integrable (fun v => charFun μ' (c • v) * conj (charFun ν' (c • v))) γ := by
    have hscale : Measurable (fun v : E => c • v) := by fun_prop
    have ha := (measurable_charFun (μ := μ')).comp hscale
    have hb := (measurable_charFun (μ := ν')).comp hscale
    apply Integrable.mono (integrable_const (1 : ℝ))
      (ha.mul (Complex.continuous_conj.measurable.comp hb)).aestronglyMeasurable
    filter_upwards with v
    change ‖charFun μ' (c • v) * conj (charFun ν' (c • v))‖ ≤ ‖(1 : ℝ)‖
    rw [norm_mul, Complex.norm_conj, norm_one]
    exact mul_le_one₀ (norm_charFun_le_one _) (norm_nonneg _) (norm_charFun_le_one _)
  have hconv (μ' ν' : Measure E) [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν'] :
      gaussianInteraction t μ' ν' =
        ∫ v, (charFun μ' (c • v) * conj (charFun ν' (c • v))).re ∂γ := by
    have h := congrArg Complex.re (gaussianInteraction_complex t ht μ' ν')
    change gaussianInteraction t μ' ν' =
      (∫ v, charFun μ' (c • v) * conj (charFun ν' (c • v)) ∂γ).re at h
    exact h.trans (by
      simpa only [RCLike.re_eq_complex_re] using (integral_re (hcomplex μ' ν')).symm)
  have hmi (μ' ν' : Measure E) [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν'] :
      Integrable (fun v => (charFun μ' (c • v) * conj (charFun ν' (c • v))).re) γ := by
    exact (hcomplex μ' ν').re
  rw [hconv μ μ, hconv ν ν, hconv μ ν, hconv ν μ,
    ← integral_add' (hmi μ μ) (hmi ν ν),
    ← integral_sub' ((hmi μ μ).add (hmi ν ν)) (hmi μ ν),
    ← integral_sub' (((hmi μ μ).add (hmi ν ν)).sub (hmi μ ν)) (hmi ν μ)]
  apply integral_congr_ae
  filter_upwards with v
  change ((A v * conj (A v)).re + (B v * conj (B v)).re -
    (A v * conj (B v)).re) - (B v * conj (A v)).re = ‖A v - B v‖^2
  have hsq : ((A v - B v) * conj (A v - B v)).re = ‖A v - B v‖^2 := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [map_sub] at hsq
  simp only [Complex.sub_re, sub_mul, mul_sub] at hsq
  linarith

theorem gaussianInteraction_difference_nonneg (t : ℝ) (ht : 0 ≤ t)
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ gaussianInteraction t μ μ + gaussianInteraction t ν ν -
      gaussianInteraction t μ ν - gaussianInteraction t ν μ := by
  rw [gaussianInteraction_difference_eq_integral t ht μ ν]
  exact integral_nonneg (fun _ => sq_nonneg _)

private theorem stdGaussian_open_pos : (stdGaussian E).IsOpenPosMeasure := by
  have hg : (gaussianReal 0 1).IsOpenPosMeasure := by
    refine ⟨fun U hU hne hzero => ?_⟩
    exact hU.measure_ne_zero volume hne (gaussianReal_absolutelyContinuous' 0 one_ne_zero hzero)
  unfold stdGaussian
  apply Continuous.isOpenPosMeasure_map
  · fun_prop
  · intro x
    exact ⟨fun i => (stdOrthonormalBasis ℝ E).repr x i, (stdOrthonormalBasis ℝ E).sum_repr x⟩

/-- At any strictly positive scale a vanishing Gaussian quadratic
energy forces equality of the two probability measures. -/
theorem eq_of_gaussianInteraction_difference_eq_zero (t : ℝ) (ht : 0 < t)
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (heq : gaussianInteraction t μ μ + gaussianInteraction t ν ν -
      gaussianInteraction t μ ν - gaussianInteraction t ν μ = 0) : μ = ν := by
  let c := Real.sqrt (2*t)
  have hc : 0 < c := Real.sqrt_pos.2 (by positivity)
  let γ := stdGaussian E
  have hopen : γ.IsOpenPosMeasure := stdGaussian_open_pos
  let A (v : E) := charFun μ (c • v)
  let B (v : E) := charFun ν (c • v)
  have hAc : Continuous A := continuous_charFun.comp (continuous_const.smul continuous_id)
  have hBc : Continuous B := continuous_charFun.comp (continuous_const.smul continuous_id)
  have hD : Integrable (fun v => ‖A v-B v‖^2) γ := by
    apply Integrable.mono (integrable_const (4 : ℝ)) ((hAc.sub hBc).norm.pow 2).aestronglyMeasurable
    filter_upwards with v
    change ‖‖A v - B v‖ ^ 2‖ ≤ ‖(4:ℝ)‖
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    have hab : ‖A v - B v‖ ≤ 2 := (norm_sub_le _ _).trans (by
      have ha := norm_charFun_le_one (μ := μ) (c • v)
      have hb := norm_charFun_le_one (μ := ν) (c • v)
      change ‖A v‖ ≤ 1 at ha
      change ‖B v‖ ≤ 1 at hb
      linarith)
    nlinarith [norm_nonneg (A v-B v)]
  rw [gaussianInteraction_difference_eq_integral t ht.le μ ν] at heq
  have hae := (integral_eq_zero_iff_of_nonneg (fun v => sq_nonneg ‖A v-B v‖) hD).mp heq
  have hab : A =ᵐ[γ] B := by
    filter_upwards [hae] with v hv
    exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa using hv))
  have hAB := Measure.eq_of_ae_eq hab hAc hBc
  apply Measure.ext_of_charFun
  funext w
  have h := congrFun hAB (c⁻¹ • w)
  simpa only [A, B, smul_smul, mul_inv_cancel₀ hc.ne', one_smul] using h

end SpringerLean
