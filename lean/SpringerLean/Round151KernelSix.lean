import SpringerLean.Round150SixMatrix
import SpringerLean.Round108KernelFive

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- Six reciprocal modes in one outer row of the finite degree-six
logarithmic quotient kernel. -/
noncomputable def schoberKernelT6Row
    (a b c d e f : ℂ) : PowerSeries ℂ :=
  PowerSeries.C a * PowerSeries.X +
  PowerSeries.C b * PowerSeries.X ^ 2 +
  PowerSeries.C c * PowerSeries.X ^ 3 +
  PowerSeries.C d * PowerSeries.X ^ 4 +
  PowerSeries.C e * PowerSeries.X ^ 5 +
  PowerSeries.C f * PowerSeries.X ^ 6

/-- The finite bivariate quotient correction through row and column six,
using the actual map's forward coefficient slots b₁ through b₁₁. -/
noncomputable def schoberKernelT6
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    PowerSeries (PowerSeries ℂ) :=
  PowerSeries.X * PowerSeries.C
    (schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆) +
  PowerSeries.X ^ 2 * PowerSeries.C
    (schoberKernelT6Row b₂ b₃ b₄ b₅ b₆ b₇) +
  PowerSeries.X ^ 3 * PowerSeries.C
    (schoberKernelT6Row b₃ b₄ b₅ b₆ b₇ b₈) +
  PowerSeries.X ^ 4 * PowerSeries.C
    (schoberKernelT6Row b₄ b₅ b₆ b₇ b₈ b₉) +
  PowerSeries.X ^ 5 * PowerSeries.C
    (schoberKernelT6Row b₅ b₆ b₇ b₈ b₉ b₁₀) +
  PowerSeries.X ^ 6 * PowerSeries.C
    (schoberKernelT6Row b₆ b₇ b₈ b₉ b₁₀ b₁₁)

/-- Finite `-log(1-T)` through power six. Any higher power vanishes in
matrix entries with both reciprocal indices at most six. -/
noncomputable def schoberKernelQ6
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    PowerSeries (PowerSeries ℂ) :=
  let T := schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
      PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
      PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4 +
      PowerSeries.C (PowerSeries.C ((5 : ℂ)⁻¹)) * T ^ 5 +
      PowerSeries.C (PowerSeries.C ((6 : ℂ)⁻¹)) * T ^ 6

theorem schoberKernelQ6_outer_one
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    PowerSeries.coeff 1
      (schoberKernelQ6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) =
      schoberKernelT6Row b₁ b₂ b₃ b₄ b₅ b₆ := by
  have hT0 : PowerSeries.constantCoeff
      (schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) = 0 := by
    simp [schoberKernelT6]
  simp [schoberKernelQ6, schoberKernelT6,
    PowerSeries.coeff_one_pow, hT0]

theorem schoberKernelQ6_first_row
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    let Q := schoberKernelQ6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
    schoberBiCoeff 1 1 Q = b₁ ∧
    schoberBiCoeff 2 1 Q = b₂ ∧
    schoberBiCoeff 3 1 Q = b₃ ∧
    schoberBiCoeff 4 1 Q = b₄ ∧
    schoberBiCoeff 5 1 Q = b₅ ∧
    schoberBiCoeff 6 1 Q = b₆ := by
  dsimp only
  simp only [schoberBiCoeff, schoberKernelQ6_outer_one]
  simp [schoberKernelT6Row, PowerSeries.coeff_X_pow]

/-- The first row of the genuine six-Faber mode matrix agrees entrywise
with the finite logarithmic kernel for the same actual map. -/
theorem sixthActualFaberMode_first_row_eq_kernel
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (j : Fin 6) :
    sixthActualFaberMode F 0 j =
      schoberBiCoeff (j.val + 1) 1
        (schoberKernelQ6
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
          (exteriorForwardCoeff F 9) (exteriorForwardCoeff F 10)
          (exteriorForwardCoeff F 11)) := by
  rcases schoberKernelQ6_first_row
      (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
      (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
      (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
      (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
      (exteriorForwardCoeff F 9) (exteriorForwardCoeff F 10)
      (exteriorForwardCoeff F 11) with
    ⟨h1, h2, h3, h4, h5, h6⟩
  fin_cases j
  · simp only [sixthActualFaberMode, ↓reduceIte,
      Fin.val_zero, Nat.zero_add, Nat.reduceAdd]
    rw [actualTaylorCoeff_exteriorPhi_succ F hc 1]
    exact h1.symm
  · simp only [sixthActualFaberMode, ↓reduceIte,
      Fin.val_one, Nat.reduceAdd]
    rw [actualTaylorCoeff_exteriorPhi_succ F hc 2]
    exact h2.symm
  · simp only [sixthActualFaberMode, ↓reduceIte,
      Fin.val_two, Nat.reduceAdd]
    rw [actualTaylorCoeff_exteriorPhi_succ F hc 3]
    exact h3.symm
  · simp only [sixthActualFaberMode, ↓reduceIte, Nat.reduceAdd]
    rw [actualTaylorCoeff_exteriorPhi_succ F hc 4]
    exact h4.symm
  · simp only [sixthActualFaberMode, ↓reduceIte, Nat.reduceAdd]
    rw [actualTaylorCoeff_exteriorPhi_succ F hc 5]
    exact h5.symm
  · simp only [sixthActualFaberMode, ↓reduceIte, Nat.reduceAdd]
    rw [actualTaylorCoeff_exteriorPhi_succ F hc 6]
    exact h6.symm

end SpringerLean
