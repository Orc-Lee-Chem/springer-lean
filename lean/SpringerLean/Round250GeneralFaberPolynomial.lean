import SpringerLean.Round249FaberLogFactorization
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace SpringerLean
open PowerSeries

/-- Faber polynomials defined uniformly by their formal logarithmic
generating series. The independent variable belongs to Polynomial A. -/
noncomputable def generalFaberPolynomial
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (f : PowerSeries A) (n : ℕ) : Polynomial A :=
  (n : Polynomial A) * PowerSeries.coeff n
    (-PowerSeries.logOf
      (PowerSeries.map Polynomial.C (1 + PowerSeries.X * f) -
        PowerSeries.C Polynomial.X * PowerSeries.X))

/-- General Faber/logarithmic-kernel coefficient identity. The coefficient
map may be the standard embedding into Laurent series; no Grunsky bound
or coefficient identity is assumed. -/
theorem generalFaberPolynomial_eval_kernel
    {A B : Type*} [CommRing A] [Field B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : PowerSeries A) (hf : PowerSeries.constantCoeff f = 0)
    (h : PowerSeries A →+* B) (hy : h PowerSeries.X ≠ 0)
    (n : ℕ) :
    let φ := 1 + PowerSeries.X * f
    let p := (h PowerSeries.X)⁻¹
    let w := p * h φ
    (Polynomial.eval₂RingHom (h.comp PowerSeries.C) w)
        (generalFaberPolynomial f (n + 1)) =
      p ^ (n + 1) + ((n + 1 : ℕ) : B) *
        PowerSeries.coeff (n + 1)
          (-PowerSeries.logOf
            (1 - PowerSeries.map h (formalFaberKernel f))) := by
  dsimp only
  let φ := 1 + PowerSeries.X * f
  let p := (h PowerSeries.X)⁻¹
  let w := p * h φ
  let e : Polynomial A →+* B :=
    Polynomial.eval₂RingHom (h.comp PowerSeries.C) w
  let S : PowerSeries (Polynomial A) :=
    PowerSeries.map Polynomial.C φ -
      PowerSeries.C Polynomial.X * PowerSeries.X
  have hS : PowerSeries.constantCoeff S = 1 := by
    simp [S, φ, ← PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_zero_X_mul]
  have he : e.comp Polynomial.C = h.comp PowerSeries.C := by
    ext a
    simp [e]
  have hmap : PowerSeries.map e (PowerSeries.map Polynomial.C φ) =
      PowerSeries.map (h.comp PowerSeries.C) φ := by
    change PowerSeries.map (e.comp Polynomial.C) φ = _
    rw [he]
  have heval : PowerSeries.map e (-PowerSeries.logOf S) =
      -PowerSeries.logOf
        (PowerSeries.map (h.comp PowerSeries.C) φ -
          PowerSeries.C w * PowerSeries.X) := by
    rw [map_neg, formal_logOf_map e S hS]
    congr 1
    dsimp only [S]
    rw [map_sub, map_mul, PowerSeries.map_C, PowerSeries.map_X, hmap]
    simp [e]
  have hc := congrArg (PowerSeries.coeff (n + 1)) heval
  simp only [PowerSeries.coeff_map] at hc
  change e (((n + 1 : ℕ) : Polynomial A) * PowerSeries.coeff (n + 1)
    (-PowerSeries.logOf S)) = _
  rw [map_mul, map_natCast, hc]
  have hlog := formalFaberKernel_mapped_log_identity f hf h hy
  change -PowerSeries.logOf
      (PowerSeries.map (h.comp PowerSeries.C) φ - PowerSeries.C w * PowerSeries.X) =
    -PowerSeries.logOf (1 - PowerSeries.C p * PowerSeries.X) +
      (-PowerSeries.logOf (1 - PowerSeries.map h (formalFaberKernel f))) at hlog
  rw [hlog, map_add, mul_add, formal_linear_log_coeff_succ p n]

end SpringerLean
