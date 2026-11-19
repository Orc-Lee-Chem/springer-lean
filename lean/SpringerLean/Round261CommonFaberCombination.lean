import SpringerLean.Round260ReciprocalFactorLinear
import SpringerLean.Round257AllOrderActualFaber

namespace SpringerLean
open PowerSeries

noncomputable def exteriorFaberCombinationPolynomial
    (F : ℂ → ℂ) (N : ℕ) (α : Fin N → ℂ) : Polynomial ℂ :=
  ∑ i : Fin N, Polynomial.C (α i) *
    exteriorGeneralFaberPolynomial F (i.val + 1)

noncomputable def exteriorFaberCombinationFactor
    (F : ℂ → ℂ) (N : ℕ) (α : Fin N → ℂ) : ℂ → ℂ :=
  polynomialReciprocalFactor F (exteriorFaberCombinationPolynomial F N α) N

theorem exteriorFaberCombinationPolynomial_natDegree_le
    (F : ℂ → ℂ) (N : ℕ) (α : Fin N → ℂ) :
    (exteriorFaberCombinationPolynomial F N α).natDegree ≤ N := by
  unfold exteriorFaberCombinationPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  calc
    _ ≤ (Polynomial.C (α i)).natDegree +
        (exteriorGeneralFaberPolynomial F (i.val + 1)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + (i.val + 1) := add_le_add (by simp)
      (generalFaberPolynomial_natDegree_le (exteriorFormalForward F) (i.val + 1))
    _ ≤ N := by omega

/-- A common leading frequency exposes every positive Fourier mode and
every Grunsky row of an arbitrary finite complex Faber combination. -/
theorem exteriorFaberCombinationFormalFactor_eq
    (F : ℂ → ℂ) (N : ℕ) (α : Fin N → ℂ) :
    polynomialFormalReciprocalFactor
        (formalExteriorPhi (exteriorFormalForward F))
        (exteriorFaberCombinationPolynomial F N α) N =
      (∑ i : Fin N, PowerSeries.C (α i) *
        PowerSeries.X ^ (N - (i.val + 1))) +
      PowerSeries.X ^ N *
        ∑ i : Fin N, PowerSeries.C (α i * ((i.val + 1 : ℕ) : ℂ)) *
          PowerSeries.coeff (i.val + 1) (exteriorFormalGrunskyKernel F) := by
  unfold exteriorFaberCombinationPolynomial
  rw [polynomialFormalReciprocalFactor_sum]
  simp_rw [polynomialFormalReciprocalFactor_const_mul]
  have hterm (i : Fin N) :
      PowerSeries.C (α i) *
          polynomialFormalReciprocalFactor
            (formalExteriorPhi (exteriorFormalForward F))
            (exteriorGeneralFaberPolynomial F (i.val + 1)) N =
        PowerSeries.C (α i) * PowerSeries.X ^ (N - (i.val + 1)) +
          PowerSeries.X ^ N *
            (PowerSeries.C (α i * ((i.val + 1 : ℕ) : ℂ)) *
              PowerSeries.coeff (i.val + 1) (exteriorFormalGrunskyKernel F)) := by
    have hi : i.val + 1 ≤ N := by omega
    have hP : (exteriorGeneralFaberPolynomial F (i.val + 1)).natDegree ≤ i.val + 1 :=
      generalFaberPolynomial_natDegree_le (exteriorFormalForward F) (i.val + 1)
    rw [polynomialFormalReciprocalFactor_shift _
      (exteriorGeneralFaberPolynomial F (i.val + 1)) (i.val + 1) N hP hi,
      exteriorGeneralFaberFormalFactor_normalization F i.val]
    have hpow : (PowerSeries.X : PowerSeries ℂ) ^ (N - (i.val + 1)) *
        PowerSeries.X ^ (i.val + 1) = PowerSeries.X ^ N := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    rw [map_mul]
    calc
      _ = PowerSeries.C (α i) * PowerSeries.X ^ (N - (i.val + 1)) +
          (PowerSeries.X ^ (N - (i.val + 1)) * PowerSeries.X ^ (i.val + 1)) *
            (PowerSeries.C (α i) * PowerSeries.C ((i.val + 1 : ℕ) : ℂ) *
              PowerSeries.coeff (i.val + 1) (exteriorFormalGrunskyKernel F)) := by ring
      _ = _ := by rw [hpow]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem exteriorFaberCombination_actualTaylorSeries
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (N : ℕ) (α : Fin N → ℂ) :
    actualTaylorSeries (exteriorFaberCombinationFactor F N α) =
      (∑ i : Fin N, PowerSeries.C (α i) *
        PowerSeries.X ^ (N - (i.val + 1))) +
      PowerSeries.X ^ N *
        ∑ i : Fin N, PowerSeries.C (α i * ((i.val + 1 : ℕ) : ℂ)) *
          PowerSeries.coeff (i.val + 1) (exteriorFormalGrunskyKernel F) := by
  rw [exteriorFaberCombinationFactor,
    polynomialReciprocalFactor_actualTaylorSeries F hc,
    exteriorFaberCombinationFormalFactor_eq]

end SpringerLean
