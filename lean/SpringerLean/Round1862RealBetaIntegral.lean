import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

open MeasureTheory Set

namespace SpringerLean

noncomputable def radialBetaIntegral (s t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x ^ (s - 1) * (1 - x) ^ (t - 1)

theorem complex_betaIntegral_eq_radialBetaIntegral (s t : ℝ) :
    Complex.betaIntegral (s : ℂ) (t : ℂ) = (radialBetaIntegral s t : ℂ) := by
  rw [Complex.betaIntegral, radialBetaIntegral, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x hx
  have hx' : x ∈ Ioc (0 : ℝ) 1 := by simpa using hx
  have hxpow := Complex.ofReal_cpow hx'.1.le (s - 1)
  have hypow := Complex.ofReal_cpow (sub_nonneg.mpr hx'.2) (t - 1)
  push_cast at hxpow hypow
  push_cast
  rw [← hxpow, ← hypow]

/-- The real beta formula is derived from the locked library's proved
complex formula, with all real-power conventions identified. -/
theorem gamma_mul_gamma_eq_radialBetaIntegral
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Real.Gamma s * Real.Gamma t = Real.Gamma (s + t) * radialBetaIntegral s t := by
  have hh := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (s : ℂ)) (t := (t : ℂ)) (by simpa using hs) (by simpa using ht)
  rw [complex_betaIntegral_eq_radialBetaIntegral,
    ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul] at hh
  exact Complex.ofReal_inj.mp hh

end SpringerLean

#print axioms SpringerLean.gamma_mul_gamma_eq_radialBetaIntegral
