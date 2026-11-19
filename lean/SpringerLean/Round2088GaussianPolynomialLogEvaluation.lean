import SpringerLean.Round2086GaussianLogMoment
import Mathlib.Algebra.Polynomial.Degree.Operations

open MeasureTheory ProbabilityTheory Filter Set Polynomial
open scoped BigOperators

namespace SpringerLean

/-- Exact logarithmic mean of a nonzero Gaussian linear combination,
and the uniform-in-scale bound needed for the product integration. -/
theorem gaussian_complex_sum_log_moment {ι : Type*} [Fintype ι] (b : ι → ℂ)
    (hvar : 0 < ∑ i, ‖b i‖ ^ 2) :
    let γ := stdGaussian (EuclideanSpace ℂ ι)
    let s := Real.sqrt (∑ i, ‖b i‖ ^ 2)
    let f : EuclideanSpace ℂ ι → ℂ := fun ξ => ∑ i, ξ i * b i
    (∀ᵐ ξ ∂γ, f ξ ≠ 0) ∧ Integrable (fun ξ => Real.log ‖f ξ‖) γ ∧
      ((∫ ξ, Real.log ‖f ξ‖ ∂γ) =
        Real.log s + ∫ z, Real.log ‖z‖ ∂stdGaussian ℂ) ∧
      (∫ ξ, ‖Real.log ‖f ξ‖‖ ∂γ) ≤
        ‖Real.log s‖ + ∫ z, ‖Real.log ‖z‖‖ ∂stdGaussian ℂ := by
  dsimp only
  let γ := stdGaussian (EuclideanSpace ℂ ι)
  let ν := stdGaussian ℂ
  let s := Real.sqrt (∑ i, ‖b i‖ ^ 2)
  let f : EuclideanSpace ℂ ι → ℂ := fun ξ => ∑ i, ξ i * b i
  let g : ℂ → ℂ := fun z => s • z
  let L := fun z : ℂ => Real.log ‖z‖
  have hmap : γ.map f = ν.map g := stdGaussian_map_complex_sum b
  have hf : Measurable f := by unfold f; fun_prop
  have hg : Measurable g := by unfold g; fun_prop
  have hL : Measurable L := Real.measurable_log.comp continuous_norm.measurable
  have hs : 0 < s := Real.sqrt_pos.2 hvar
  have hne : ∀ᵐ z ∂ν, g z ≠ 0 := by
    filter_upwards [stdGaussian_complex_ae_ne_zero] with z hz
    exact smul_ne_zero hs.ne' hz
  have hbad : ∀ᵐ ξ ∂γ, f ξ ≠ 0 := by
    apply (ae_map_iff hf.aemeasurable (measurableSet_singleton (0:ℂ)).compl).mp
    rw [hmap]
    exact (ae_map_iff hg.aemeasurable (measurableSet_singleton (0:ℂ)).compl).mpr hne
  have hlog : (fun z => L (g z)) =ᵐ[ν] fun z => Real.log s + L z := by
    filter_upwards [stdGaussian_complex_ae_ne_zero] with z hz
    simp only [L, g, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    exact Real.log_mul hs.ne' (norm_ne_zero_iff.mpr hz)
  have hi : Integrable (fun z => L (g z)) ν :=
    ((integrable_const (Real.log s)).add stdGaussian_complex_integrable_log_norm).congr hlog.symm
  have hif : Integrable (fun ξ => L (f ξ)) γ := by
    apply (integrable_map_measure hL.aestronglyMeasurable hf.aemeasurable).mp
    rw [hmap]
    exact (integrable_map_measure hL.aestronglyMeasurable hg.aemeasurable).mpr hi
  refine ⟨hbad, hif, ?_, ?_⟩
  · change (∫ ξ, L (f ξ) ∂γ) = Real.log s + ∫ z, L z ∂ν
    rw [← integral_map hf.aemeasurable hL.aestronglyMeasurable, hmap,
      integral_map hg.aemeasurable hL.aestronglyMeasurable, integral_congr_ae hlog,
      integral_add (integrable_const _) stdGaussian_complex_integrable_log_norm,
      integral_const, probReal_univ, one_smul]
  · change (∫ ξ, ‖L (f ξ)‖ ∂γ) ≤ ‖Real.log s‖ + ∫ z, ‖L z‖ ∂ν
    rw [← integral_map hf.aemeasurable hL.norm.aestronglyMeasurable, hmap,
      integral_map hg.aemeasurable hL.norm.aestronglyMeasurable]
    have hleAE : ∀ᵐ z ∂ν, ‖L (g z)‖ ≤ ‖Real.log s‖ + ‖L z‖ := by
      filter_upwards [hlog] with z hz
      change L (g z) = Real.log s + L z at hz
      rw [hz]
      exact norm_add_le _ _
    have hLi : Integrable (fun z => ‖L z‖) ν := stdGaussian_complex_integrable_log_norm.norm
    have hle := integral_mono_ae hi.norm ((integrable_const ‖Real.log s‖).add hLi) hleAE
    change (∫ z, ‖L (g z)‖ ∂ν) ≤ ∫ z, ‖Real.log s‖ + ‖L z‖ ∂ν at hle
    rw [integral_add (integrable_const _) hLi, integral_const, probReal_univ, one_smul] at hle
    exact hle

/-- The auxiliary polynomial for the upper factor estimate. -/
noncomputable def gaussianAuxiliaryPolynomial {N : ℕ} (B : Fin N → ℂ) (m : ℕ)
    (ξ : EuclideanSpace ℂ (Fin N)) : ℂ[X] :=
  ∑ i : Fin N, C (ξ i) * (X-C (B i))^m

@[simp] theorem gaussianAuxiliaryPolynomial_eval {N : ℕ} (B : Fin N → ℂ)
    (m : ℕ) (ξ : EuclideanSpace ℂ (Fin N)) (z : ℂ) :
    (gaussianAuxiliaryPolynomial B m ξ).eval z = ∑ i : Fin N, ξ i * (z-B i)^m := by
  simp [gaussianAuxiliaryPolynomial, eval_finsetSum, eval_mul, eval_pow, eval_sub]

theorem gaussianAuxiliaryPolynomial_degree {N : ℕ} (B : Fin N → ℂ)
    (m : ℕ) (ξ : EuclideanSpace ℂ (Fin N)) (hξ : (∑ i : Fin N, ξ i) ≠ 0) :
    (gaussianAuxiliaryPolynomial B m ξ).natDegree = m ∧
      gaussianAuxiliaryPolynomial B m ξ ≠ 0 := by
  let Q := gaussianAuxiliaryPolynomial B m ξ
  have hdeg (i : Fin N) : ((X-C (B i))^m : ℂ[X]).natDegree = m := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  have hcoeff (i : Fin N) : (((X-C (B i))^m : ℂ[X]).coeff m) = 1 := by
    have h := ((monic_X_sub_C (B i)).pow m).leadingCoeff
    change (((X-C (B i))^m : ℂ[X]).coeff (((X-C (B i))^m : ℂ[X]).natDegree)) = 1 at h
    rwa [hdeg i] at h
  have hcm : Q.coeff m = ∑ i : Fin N, ξ i := by
    simp only [Q, gaussianAuxiliaryPolynomial, finsetSum_coeff, coeff_C_mul, hcoeff, mul_one]
  have hcm0 : Q.coeff m ≠ 0 := hcm.trans_ne hξ
  have hbound : Q.natDegree ≤ m := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro r hr
    simp only [Q, gaussianAuxiliaryPolynomial, finsetSum_coeff, coeff_C_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [coeff_eq_zero_of_natDegree_lt ((hdeg i).trans_lt hr), mul_zero]
  exact ⟨le_antisymm hbound (le_natDegree_of_ne_zero hcm0),
    fun h => hcm0 (by rw [show Q = 0 from h]; simp)⟩

end SpringerLean
