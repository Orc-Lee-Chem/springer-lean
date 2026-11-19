import SpringerLean.Round2087DeterministicFactorEstimate
import SpringerLean.Round2088GaussianPolynomialLogEvaluation

open MeasureTheory ProbabilityTheory Polynomial Set Filter
open scoped BigOperators

namespace SpringerLean

/-- The logarithm of the scale of the Gaussian evaluation law. -/
noncomputable def finiteGaussianLogScale {N : ℕ} (B : Fin N → ℂ) (m : ℕ) (z : ℂ) : ℝ :=
  Real.log (Real.sqrt (∑ i : Fin N, ‖(z-B i)^m‖ ^ 2))

private theorem gaussianPolynomial_scale_pos {N : ℕ} (B : Fin N → ℂ)
    (i j : Fin N) (hij : B i ≠ B j) (m : ℕ) (z : ℂ) :
    0 < ∑ l : Fin N, ‖(z-B l)^m‖^2 := by
  have h : ∃ l : Fin N, z ≠ B l := by
    by_cases h : z = B i
    · exact ⟨j,h.trans_ne hij⟩
    · exact ⟨i,h⟩
  obtain ⟨l,hl⟩ := h
  exact (pow_pos (norm_pos_iff.mpr (pow_ne_zero m (sub_ne_zero.mpr hl))) 2).trans_le
    (Finset.single_le_sum (f := fun l : Fin N => ‖(z-B l)^m‖^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ l))

theorem finiteGaussianLogScale_continuous {N : ℕ} (B : Fin N → ℂ)
    (i j : Fin N) (hij : B i ≠ B j) (m : ℕ) : Continuous (finiteGaussianLogScale B m) := by
  unfold finiteGaussianLogScale
  apply (show Continuous (fun z => Real.sqrt (∑ l : Fin N, ‖(z-B l)^m‖^2)) from
    by fun_prop).log
  exact fun z => (Real.sqrt_pos.2 (gaussianPolynomial_scale_pos B i j hij m z)).ne'

/-- The averaged log estimate on the actual boundary law. No measure
of random roots is needed. The Fubini kernel is evaluated polynomials. -/
theorem linear_product_log_bound_gaussian_average
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (hK : (exteriorOmitted F).Nonempty)
    (n : ℕ) (a : Fin n → ℂ)
    (N : ℕ) (B : Fin N → ℂ) (i j : Fin N) (hij : B i ≠ B j) (m : ℕ) :
    (∑ l : Fin n, finiteGaussianLogScale B m (a l)) ≤
      (m:ℝ) * Real.log (continuumPolynomialNorm (exteriorOmitted F)
        (∏ l : Fin n, (X-C (a l)))) +
      (n:ℝ) * ∫ z, finiteGaussianLogScale B m z ∂actualExteriorBoundaryProbability F := by
  let E := EuclideanSpace ℂ (Fin N)
  let γ := stdGaussian E
  let μ := actualExteriorBoundaryProbability F
  let Q := gaussianAuxiliaryPolynomial B m
  let K := exteriorOmitted F
  let P : ℂ[X] := ∏ l : Fin n, (X-C (a l))
  let M := continuumPolynomialNorm K P
  let H := finiteGaussianLogScale B m
  let L (ξ : E) (z : ℂ) := Real.log ‖(Q ξ).eval z‖
  let c0 := ∫ z, Real.log ‖z‖ ∂stdGaussian ℂ
  let c1 := ∫ z, ‖Real.log ‖z‖‖ ∂stdGaussian ℂ
  have hprob : IsProbabilityMeasure μ := ⟨actualExteriorBoundaryProbability_univ F hF⟩
  have hcompact := exteriorOmitted_isCompact F hF
  have hμ : K ∈ ae μ := actualExteriorBoundaryProbability_ae_mem_omitted F hF hcompact.isClosed
  have hs (z : ℂ) := gaussianPolynomial_scale_pos B i j hij m z
  have hcont : Continuous H := finiteGaussianLogScale_continuous B i j hij m
  have hslice (z : ℂ) :
      (∀ᵐ ξ ∂γ, (Q ξ).eval z ≠ 0) ∧ Integrable (fun ξ => L ξ z) γ ∧
        ((∫ ξ, L ξ z ∂γ) = H z + c0) ∧
        (∫ ξ, ‖L ξ z‖ ∂γ) ≤ ‖H z‖ + c1 := by
    simpa only [Q, L, H, finiteGaussianLogScale, c0, c1, gaussianAuxiliaryPolynomial_eval] using
      gaussian_complex_sum_log_moment (fun l : Fin N => (z-B l)^m) (hs z)
  have hmeas : Measurable (Function.uncurry L) := by
    apply Real.measurable_log.comp
    change Measurable (fun p : E × ℂ => ‖(Q p.1).eval p.2‖)
    rw [show (fun p : E × ℂ => ‖(Q p.1).eval p.2‖) =
        (fun p : E × ℂ => ‖∑ l : Fin N, p.1 l * (p.2-B l)^m‖) from
      funext (fun p => congrArg norm (gaussianAuxiliaryPolynomial_eval B m p.1 p.2))]
    apply Continuous.measurable
    apply Continuous.norm
    apply continuous_finset_sum _
    intro l _
    have hc : Continuous (fun p : E × ℂ => p.1 l) :=
      (PiLp.continuous_apply 2 (fun _ : Fin N => ℂ) l).comp continuous_fst
    exact hc.mul ((continuous_snd.sub continuous_const).pow m)
  obtain ⟨B0,hB0⟩ := (hcompact.image hcont).isBounded.exists_norm_le
  have hnormBound : ∀ᵐ z ∂μ, ‖H z‖ ≤ max B0 0 := by
    filter_upwards [hμ] with z hz
    exact (hB0 _ ⟨z,hz,rfl⟩).trans (le_max_left _ _)
  have hHμ : Integrable H μ := by
    apply Integrable.mono (integrable_const (max B0 0)) hcont.aestronglyMeasurable
    simpa only [Real.norm_of_nonneg (le_max_right B0 0)] using hnormBound
  have hmix : Integrable (Function.uncurry L) (γ.prod μ) := by
    apply (integrable_prod_iff' hmeas.aestronglyMeasurable).mpr
    refine ⟨.of_forall (fun z => (hslice z).2.1), ?_⟩
    have hc1 : 0 ≤ c1 := integral_nonneg (fun _ => norm_nonneg _)
    have hleft : AEStronglyMeasurable (fun z => ∫ ξ, ‖L ξ z‖ ∂γ) μ :=
      (hmeas.norm.stronglyMeasurable.integral_prod_left' (μ := γ)).aestronglyMeasurable
    apply Integrable.mono (integrable_const (max B0 0 + c1)) hleft
    filter_upwards [hnormBound] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)),
      Real.norm_of_nonneg (add_nonneg (le_max_right B0 0) hc1)]
    exact (hslice z).2.2.2.trans (add_le_add hz le_rfl)
  have hGauss0 : ∀ᵐ ξ ∂γ, (∑ l : Fin N, ξ l) ≠ 0 := by
    have hN : 0 < N := i.isLt.pos
    have hvar : 0 < ∑ l : Fin N, ‖(1:ℂ)‖^2 := by
      simpa only [norm_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, Nat.cast_pos] using hN
    simpa only [mul_one] using (gaussian_complex_sum_log_moment (fun _ : Fin N => (1:ℂ)) hvar).1
  have hdet : ∀ᵐ ξ ∂γ, (∑ l : Fin n, L ξ (a l)) ≤
      (m:ℝ) * Real.log M + (n:ℝ) * ∫ z, L ξ z ∂μ := by
    filter_upwards [hGauss0, ae_all_iff.mpr (fun l : Fin n => (hslice (a l)).1)] with ξ hξ he
    obtain ⟨hdeg,hQ⟩ := gaussianAuxiliaryPolynomial_degree B m ξ hξ
    have hlo := auxiliary_polynomial_linear_product_log_bound F hF hK n a P rfl
      (exterior_linear_product_norm_pos F hF n a) (Q ξ) hQ he
    rw [hdeg] at hlo
    exact hlo
  have hleftI : Integrable (fun ξ => ∑ l : Fin n, L ξ (a l)) γ :=
    integrable_finsetSum _ (fun l _ => (hslice (a l)).2.1)
  have hrightInner : Integrable (fun ξ => ∫ z, L ξ z ∂μ) γ := hmix.integral_prod_left
  have hrightI : Integrable (fun ξ => (m:ℝ)*Real.log M + (n:ℝ)*∫ z, L ξ z ∂μ) γ :=
    (integrable_const _).add (hrightInner.const_mul _)
  have hev := integral_mono_ae hleftI hrightI hdet
  rw [integral_finsetSum _ (fun l _ => (hslice (a l)).2.1),
    integral_add (integrable_const ((m:ℝ)*Real.log M)) (hrightInner.const_mul (n:ℝ)),
    integral_const, probReal_univ, one_smul, integral_const_mul] at hev
  have hmixEq : (∫ ξ, ∫ z, L ξ z ∂μ ∂γ) = (∫ z, H z ∂μ) + c0 := by
    rw [integral_integral_swap hmix]
    simp_rw [fun z => (hslice z).2.2.1]
    rw [integral_add hHμ (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [hmixEq] at hev
  have hlocal (l : Fin n) := (hslice (a l)).2.2.1
  simp_rw [hlocal, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hev
  change _ ≤ (m:ℝ) * Real.log M + (n:ℝ)*∫ z, H z ∂μ
  linarith

end SpringerLean
