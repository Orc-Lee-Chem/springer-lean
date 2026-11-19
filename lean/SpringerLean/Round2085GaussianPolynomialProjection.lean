import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory ProbabilityTheory Module Complex
open scoped BigOperators RealInnerProductSpace ComplexConjugate

namespace SpringerLean

/-- An adjoint identity and a norm identity identify a linear image
of the standard Gaussian with a scalar dilation. -/
theorem stdGaussian_map_of_adjoint_norm
    {E H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup H]
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ H]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace H] [BorelSpace H]
    (f : E → H) (hf : Continuous f) (adj : H → E)
    (s : ℝ) (ha : ∀ x u, ⟪f x,u⟫ = ⟪x,adj u⟫)
    (hn : ∀ u, ‖adj u‖ = ‖s • u‖) :
    (stdGaussian E).map f = (stdGaussian H).map (fun u => s • u) := by
  have hcont : Continuous (fun u : H => s • u) := continuous_const.smul continuous_id
  have h1 : IsProbabilityMeasure ((stdGaussian E).map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.measurable.aemeasurable).mpr inferInstance
  have h2 : IsProbabilityMeasure ((stdGaussian H).map (fun u => s • u)) :=
    (Measure.isProbabilityMeasure_map_iff hcont.measurable.aemeasurable).mpr inferInstance
  apply Measure.ext_of_charFun
  funext u
  have hφ : AEStronglyMeasurable (fun x : H => Complex.exp (↑⟪x,u⟫ * I))
      ((stdGaussian E).map f) := by fun_prop
  have hψ : AEStronglyMeasurable (fun x : H => Complex.exp (↑⟪x,u⟫ * I))
      ((stdGaussian H).map (fun x => s • x)) := by fun_prop
  rw [charFun_apply, charFun_apply, integral_map hf.measurable.aemeasurable hφ,
    integral_map hcont.measurable.aemeasurable hψ]
  simp_rw [ha, real_inner_smul_left, ← real_inner_smul_right]
  rw [← charFun_apply, ← charFun_apply, charFun_stdGaussian, charFun_stdGaussian, hn]

/-- A complex linear combination of standard Gaussian coordinates
has the law of one standard complex Gaussian multiplied by the
Euclidean norm of the coefficient vector. -/
theorem stdGaussian_map_complex_sum {ι : Type*} [Fintype ι]
    (b : ι → ℂ) :
    (stdGaussian (EuclideanSpace ℂ ι)).map (fun x => ∑ i, x i * b i) =
      (stdGaussian ℂ).map (fun z => Real.sqrt (∑ i, ‖b i‖^2) • z) := by
  let adj (u : ℂ) : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => u * conj (b i))
  apply stdGaussian_map_of_adjoint_norm _ (by fun_prop) adj
  · intro x u
    rw [Complex.inner, PiLp.inner_apply]
    simp only [map_sum, Finset.mul_sum, Complex.re_sum, Complex.inner, WithLp.ofLp_toLp,
      map_mul, adj]
    apply Finset.sum_congr rfl
    intro i _
    ring_nf
  · intro u
    have hsum : 0 ≤ ∑ i, ‖b i‖^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hsum]
    simp only [adj, WithLp.ofLp_toLp, norm_mul, Complex.norm_conj, mul_pow, ← Finset.mul_sum]
    ring

/-- Projection of the standard complex Gaussian to the real axis
gives the standard real Gaussian. -/
theorem stdGaussian_complex_map_re :
    (stdGaussian ℂ).map Complex.re = gaussianReal 0 1 := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis Complex.orthonormalBasisOneI,
    Measure.map_map Complex.continuous_re.measurable (by fun_prop)]
  have hproj (x : Fin 2 → ℝ) :
      Complex.re (∑ i, x i • Complex.orthonormalBasisOneI i) = x 0 := by
    simp [Complex.coe_orthonormalBasisOneI, Fin.sum_univ_two, Complex.real_smul]
  simp only [Function.comp_def, hproj]
  simpa using (Measure.pi_map_eval (fun _ : Fin 2 => gaussianReal 0 1) (0 : Fin 2))

end SpringerLean
