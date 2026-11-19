import SpringerLean.Round264FaberKernelScaling
import SpringerLean.Round120FiniteNormalize

open scoped Topology

namespace SpringerLean
open PowerSeries

/-- Strong finite Grunsky inequality for every finite dimension, proved
from the original actual exterior class. No area, kernel-contraction or
regularization hypothesis remains in the public theorem. -/
theorem exterior_generalGrunsky_weighted_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (N : ℕ) (α : Fin N → ℂ) :
    (∑ j : Fin N, ((j.val + 1 : ℕ) : ℝ) *
      ‖∑ i : Fin N, α i * ((i.val + 1 : ℕ) : ℂ) *
        PowerSeries.coeff (j.val + 1)
          (PowerSeries.coeff (i.val + 1) (exteriorFormalGrunskyKernel F))‖ ^ 2) ≤
      ∑ i : Fin N, ((i.val + 1 : ℕ) : ℝ) * ‖α i‖ ^ 2 := by
  let c : Fin N → Fin N → ℂ := fun j i =>
    PowerSeries.coeff (j.val + 1)
      (PowerSeries.coeff (i.val + 1) (exteriorFormalGrunskyKernel F))
  let E : ℝ → ℝ := fun s =>
    ∑ j : Fin N, ((j.val + 1 : ℕ) : ℝ) *
      ‖∑ i : Fin N, α i * ((i.val + 1 : ℕ) : ℂ) *
        (s : ℂ) ^ ((j.val + 1) + (i.val + 1)) * c j i‖ ^ 2
  have hcont : Continuous E := by
    dsimp only [E]
    fun_prop
  have hlim : Filter.Tendsto (fun n : ℕ => E (omittedScaleSeq n))
      Filter.atTop (nhds (E 1)) :=
    hcont.continuousAt.tendsto.comp omittedScaleSeq_tendsto_one
  have hbound (n : ℕ) : E (omittedScaleSeq n) ≤
      ∑ i : Fin N, ((i.val + 1 : ℕ) : ℝ) * ‖α i‖ ^ 2 := by
    have h := rescaleExterior_generalGrunsky_weighted_contraction F hc
      (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n) N α
    simp_rw [rescaleExterior_formalGrunskyCoeff F hc (omittedScaleSeq_pos n)] at h
    simpa only [E, c, mul_assoc] using h
  have h := le_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  simpa [E, c] using h

/-- The normalized actual logarithmic Grunsky matrix is an l2 contraction
in every finite dimension N, including all finite orders required by the
Schober and rational Gram routes. -/
theorem exterior_generalGrunsky_normalized_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (N : ℕ) (v : Fin N → ℂ) :
    (∑ j : Fin N,
      ‖∑ i : Fin N,
        ((Real.sqrt ((j.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.sqrt ((i.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          PowerSeries.coeff (j.val + 1)
            (PowerSeries.coeff (i.val + 1) (exteriorFormalGrunskyKernel F)) * v i‖ ^ 2) ≤
      ∑ i : Fin N, ‖v i‖ ^ 2 := by
  let c : Fin N → Fin N → ℂ := fun j i =>
    PowerSeries.coeff (j.val + 1)
      (PowerSeries.coeff (i.val + 1) (exteriorFormalGrunskyKernel F))
  exact finiteDim_weighted_kernel_normalize N c
    (fun α => exterior_generalGrunsky_weighted_contraction F hc N α) v

end SpringerLean
