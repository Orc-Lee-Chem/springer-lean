import SpringerLean.Round292HermitianGramEnergy

namespace SpringerLean

theorem exteriorGeneralGrunsky_deficit_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (N : ℕ) (x : Fin N → ℂ) :
    0 ≤ (∑ i : Fin N, ‖x i‖ ^ 2 / ((i.val + 1 : ℕ) : ℝ)) -
      ∑ j : Fin N, ((j.val + 1 : ℕ) : ℝ) *
        ‖∑ i : Fin N, exteriorGeneralUnweightedKernel F N j i * x i‖ ^ 2 := by
  classical
  let α : Fin N → ℂ := fun i => x i / ((i.val + 1 : ℕ) : ℂ)
  have h := exterior_generalGrunsky_weighted_contraction F hc N α
  have hi (i : Fin N) : ((i.val + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero i.val)
  have hprod (i : Fin N) : α i * ((i.val + 1 : ℕ) : ℂ) = x i := by
    dsimp only [α]
    exact div_mul_cancel₀ _ (hi i)
  simp_rw [hprod] at h
  have hin : (∑ i : Fin N, ((i.val + 1 : ℕ) : ℝ) * ‖α i‖ ^ 2) =
      ∑ i : Fin N, ‖x i‖ ^ 2 / ((i.val + 1 : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hii
    simp only [α, norm_div, Complex.norm_natCast, div_pow]
    have hr : ((i.val + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hin] at h
  have hout : (∑ j : Fin N, ((j.val + 1 : ℕ) : ℝ) *
      ‖∑ i : Fin N, x i * PowerSeries.coeff (j.val + 1)
        (PowerSeries.coeff (i.val + 1) (exteriorFormalGrunskyKernel F))‖ ^ 2) =
      ∑ j : Fin N, ((j.val + 1 : ℕ) : ℝ) *
        ‖∑ i : Fin N, exteriorGeneralUnweightedKernel F N j i * x i‖ ^ 2 := by
    simp only [exteriorGeneralUnweightedKernel, mul_comm]
  rw [hout] at h
  linarith

noncomputable def universalGrunskyDeficit (N : ℕ)
    (x : Fin N → MvPolynomial ℕ ℚ) : RationalHermitianPolynomial :=
  (∑ i : Fin N, MvPolynomial.C ((((i.val + 1 : ℕ) : ℚ))⁻¹) *
    rationalHermitianNormSq (x i)) -
  ∑ j : Fin N, MvPolynomial.C (((j.val + 1 : ℕ) : ℚ)) *
    rationalHermitianNormSq (∑ i : Fin N,
      PowerSeries.coeff (j.val + 1)
        (PowerSeries.coeff (i.val + 1) universalLogGrunskyKernel) * x i)

/-- Actual-map correctness of every finite universal Grunsky deficit.
The test polynomial may depend on the same map's other coefficients. -/
theorem universalGrunskyDeficit_eval_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (N : ℕ) (x : Fin N → MvPolynomial ℕ ℚ) :
    0 ≤ (actualHermitianPolynomialEval F (universalGrunskyDeficit N x)).re := by
  have h := exteriorGeneralGrunsky_deficit_nonneg F hc N
    (fun i => actualForwardPolynomialEval F (x i))
  have heq : actualHermitianPolynomialEval F (universalGrunskyDeficit N x) =
      (((∑ i : Fin N, ‖actualForwardPolynomialEval F (x i)‖ ^ 2 /
          ((i.val + 1 : ℕ) : ℝ)) -
        ∑ j : Fin N, ((j.val + 1 : ℕ) : ℝ) *
          ‖∑ i : Fin N, exteriorGeneralUnweightedKernel F N j i *
            actualForwardPolynomialEval F (x i)‖ ^ 2 : ℝ) : ℂ) := by
    simp only [universalGrunskyDeficit, map_sub, map_sum, map_mul]
    simp_rw [rationalHermitianNormSq_eval]
    simp only [actualHermitianPolynomialEval,
      MvPolynomial.eval₂Hom_C, map_inv₀, map_natCast]
    simp only [map_sum, map_mul, universalLogGrunskyCoeff_eval,
      exteriorGeneralUnweightedKernel]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, Complex.ofReal_re]
  exact h

end SpringerLean
