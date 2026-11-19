import SpringerLean.Round281BivariateSubstitutionCoefficients
import SpringerLean.Round282TensorFunctional

namespace SpringerLean
open PowerSeries

noncomputable def formalKernelMonomial (c : ℂ) (p q : ℕ) :
    PowerSeries (PowerSeries ℂ) :=
  PowerSeries.C (PowerSeries.C c) * PowerSeries.X ^ q *
    PowerSeries.C (PowerSeries.X ^ p)

theorem formalKernelMonomial_biCoeff (c : ℂ) (p q i j : ℕ) :
    schoberBiCoeff i j (formalKernelMonomial c p q) =
      if i = p ∧ j = q then c else 0 := by
  unfold formalKernelMonomial schoberBiCoeff
  rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  by_cases hjq : j = q
  · simp only [hjq, ite_true, mul_one]
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    by_cases hip : i = p <;> simp [hip]
  · simp [hjq]

noncomputable def exteriorTruncatedGeneralKernel (F : ℂ → ℂ) (N : ℕ) :
    PowerSeries (PowerSeries ℂ) :=
  ∑ p : Fin N, ∑ q : Fin N,
    formalKernelMonomial (exteriorGeneralUnweightedKernel F N p q)
      (p.val + 1) (q.val + 1)

theorem exteriorFormalGrunskyKernel_constantCoeff (F : ℂ → ℂ) :
    PowerSeries.constantCoeff (exteriorFormalGrunskyKernel F) = 0 := by
  unfold exteriorFormalGrunskyKernel
  rw [map_neg, PowerSeries.constantCoeff_logOf (by simp), neg_zero]

theorem exteriorFormalGrunskyKernel_innerZero (F : ℂ → ℂ) (j : ℕ) :
    schoberBiCoeff 0 j (exteriorFormalGrunskyKernel F) = 0 := by
  rw [show schoberBiCoeff 0 j (exteriorFormalGrunskyKernel F) =
      schoberBiCoeff j 0 (exteriorFormalGrunskyKernel F) from
        exteriorFormalGrunskyKernel_coeff_symm F 0 j]
  simp [schoberBiCoeff, PowerSeries.coeff_zero_eq_constantCoeff,
    exteriorFormalGrunskyKernel_constantCoeff]

theorem exteriorTruncatedGeneralKernel_low_eq (F : ℂ → ℂ) (N : ℕ) :
    schoberLowEq (N + 1) (exteriorFormalGrunskyKernel F)
      (exteriorTruncatedGeneralKernel F N) := by
  intro i j hi hj
  have hsum : schoberBiCoeff i j (exteriorTruncatedGeneralKernel F N) =
      ∑ p : Fin N, ∑ q : Fin N,
        if i = p.val + 1 ∧ j = q.val + 1 then
          exteriorGeneralUnweightedKernel F N p q else 0 := by
    simp only [exteriorTruncatedGeneralKernel, schoberBiCoeff, map_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    exact formalKernelMonomial_biCoeff _ _ _ _ _
  rw [hsum]
  by_cases hi0 : i = 0
  · subst i
    rw [exteriorFormalGrunskyKernel_innerZero]
    simp
  by_cases hj0 : j = 0
  · subst j
    simp [schoberBiCoeff, PowerSeries.coeff_zero_eq_constantCoeff,
      exteriorFormalGrunskyKernel_constantCoeff]
  let ip : Fin N := ⟨i - 1, by omega⟩
  let jq : Fin N := ⟨j - 1, by omega⟩
  have heqi (p : Fin N) : i = p.val + 1 ↔ p = ip := by
    constructor
    · intro h
      apply Fin.ext
      dsimp [ip]
      omega
    · intro h
      subst p
      dsimp [ip]
      omega
  have heqj (q : Fin N) : j = q.val + 1 ↔ q = jq := by
    constructor
    · intro h
      apply Fin.ext
      dsimp [jq]
      omega
    · intro h
      subst q
      dsimp [jq]
      omega
  simp_rw [heqi, heqj]
  simp only [ite_and]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_ite_eq', Finset.sum_const_zero, Finset.mem_univ, ite_true]
  change schoberBiCoeff i j (exteriorFormalGrunskyKernel F) =
    schoberBiCoeff (ip.val + 1) (jq.val + 1) (exteriorFormalGrunskyKernel F)
  congr 1 <;> dsimp [ip, jq] <;> omega

end SpringerLean
