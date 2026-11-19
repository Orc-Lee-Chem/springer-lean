import SpringerLean.Round250GeneralFaberPolynomial
import SpringerLean.LowOrder
import Mathlib.RingTheory.LaurentSeries

namespace SpringerLean
open PowerSeries

/-- The uniform Faber polynomial generated from the same F's independently
defined actual forward Taylor coefficients. -/
noncomputable def exteriorGeneralFaberPolynomial (F : ℂ → ℂ) (n : ℕ) : Polynomial ℂ :=
  generalFaberPolynomial (exteriorFormalForward F) n

noncomputable def exteriorFormalGrunskyKernel (F : ℂ → ℂ) :
    PowerSeries (PowerSeries ℂ) :=
  -PowerSeries.logOf (1 - formalFaberKernel (exteriorFormalForward F))

/-- The Laurent series z + sum b_j z^-j written in the reciprocal variable.
Its coefficients are the actual forward derivative coefficients of F. -/
noncomputable def exteriorFormalLaurent (F : ℂ → ℂ) : LaurentSeries ℂ :=
  let h := HahnSeries.ofPowerSeries ℤ ℂ
  (h PowerSeries.X)⁻¹ * h (formalExteriorPhi (exteriorFormalForward F))

/-- All-order Faber coefficient identity for the same actual F's forward
coefficients and its canonical Laurent series. The canonical embedding
is fixed, with no assumed kernel or matrix correspondence. -/
theorem exteriorGeneralFaberPolynomial_formalLaurent_eval
    (F : ℂ → ℂ) (n : ℕ) :
    let h := HahnSeries.ofPowerSeries ℤ ℂ
    (Polynomial.eval₂RingHom (h.comp PowerSeries.C) (exteriorFormalLaurent F))
        (exteriorGeneralFaberPolynomial F (n + 1)) =
      ((h PowerSeries.X)⁻¹) ^ (n + 1) +
        ((n + 1 : ℕ) : LaurentSeries ℂ) *
          h (PowerSeries.coeff (n + 1) (exteriorFormalGrunskyKernel F)) := by
  let h := HahnSeries.ofPowerSeries ℤ ℂ
  let f := exteriorFormalForward F
  have hf : PowerSeries.constantCoeff f = 0 := by
    simpa [f, PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  have hy : h PowerSeries.X ≠ 0 := by
    intro hz
    have hx : (PowerSeries.X : PowerSeries ℂ) = 0 :=
      HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
        (by simpa [h] using hz)
    exact PowerSeries.X_ne_zero hx
  have hQ : PowerSeries.map h (exteriorFormalGrunskyKernel F) =
      -PowerSeries.logOf (1 - PowerSeries.map h (formalFaberKernel f)) := by
    unfold exteriorFormalGrunskyKernel
    rw [map_neg, formal_logOf_map h _ (by simp)]
    simp [f]
  have hcoeff := congrArg (PowerSeries.coeff (n + 1)) hQ
  simp only [PowerSeries.coeff_map] at hcoeff
  have heval := generalFaberPolynomial_eval_kernel f hf h hy n
  dsimp only at heval
  rw [← hcoeff] at heval
  simpa [exteriorGeneralFaberPolynomial, exteriorFormalLaurent,
    formalExteriorPhi, f, h] using heval

end SpringerLean
