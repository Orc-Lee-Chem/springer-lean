import SpringerLean.Round259ActualPolynomialEnergy
import SpringerLean.Round262ActualFaberModes

namespace SpringerLean
open PowerSeries

/-- Arbitrary finite full-vector weighted Grunsky inequality for every
actual regularized map. Cross terms are retained throughout. -/
theorem rescaleExterior_generalGrunsky_weighted_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (N : ℕ) (α : Fin N → ℂ) :
    (∑ j : Fin N, ((j.val + 1 : ℕ) : ℝ) *
      ‖∑ i : Fin N, α i * ((i.val + 1 : ℕ) : ℂ) *
        PowerSeries.coeff (j.val + 1)
          (PowerSeries.coeff (i.val + 1)
            (exteriorFormalGrunskyKernel (rescaleExterior s F)))‖ ^ 2) ≤
      ∑ i : Fin N, ((i.val + 1 : ℕ) : ℝ) * ‖α i‖ ^ 2 := by
  let G := rescaleExterior s F
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  have h := rescaleExterior_polynomial_negative_energy_le F hc hs0 hs1
    (exteriorFaberCombinationPolynomial G N α) N
    (exteriorFaberCombinationPolynomial_natDegree_le G N α)
  change (∑ j ∈ Finset.range N,
      ((j + 1 : ℕ) : ℝ) *
        ‖actualTaylorCoeff (exteriorFaberCombinationFactor G N α) (N + (j + 1))‖ ^ 2) ≤
    ∑ k ∈ Finset.range N,
      ((N : ℝ) - k) *
        ‖actualTaylorCoeff (exteriorFaberCombinationFactor G N α) k‖ ^ 2 at h
  rw [exteriorFaberCombination_actual_positive_energy G hcG N α] at h
  simp_rw [exteriorFaberCombination_actual_negativeCoeff G hcG N α] at h
  rw [Finset.sum_range] at h
  exact h

end SpringerLean
