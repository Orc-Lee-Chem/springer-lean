import SpringerLean.Round34PoissonComparator

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The actual harmonic filling of the unrotated slit is twice the real part. -/
theorem slitMap_one_actualHarmonic_eq_two_re (z : ℂ) :
    actualHarmonic (slitMap 1) z = (2 * z.re : ℂ) := by
  have hg : exteriorForwardGerm (slitMap 1) = fun u : ℂ => u := by
    funext u
    by_cases hu : u = 0
    · simp [exteriorForwardGerm, hu]
    · simp [exteriorForwardGerm, slitMap, hu, div_eq_mul_inv]
  simp [actualHarmonic, hg, Complex.add_re, Complex.conj_re]
  apply Complex.ext <;> simp <;> ring

/-- The factor 2 in the sought pointwise bound is attained on every
positive real radius by an actual map in the original function class. -/
theorem slitMap_one_actualHarmonic_norm_eq_two_norm
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖actualHarmonic (slitMap 1) (r : ℂ)‖ = 2 * ‖(r : ℂ)‖ := by
  rw [slitMap_one_actualHarmonic_eq_two_re]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]


/-- The sharpness witness belongs to the original centered exterior class. -/
theorem slitMap_one_actualHarmonic_sharp_witness
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    CenteredExteriorUnivalent (slitMap 1) ∧
      ‖actualHarmonic (slitMap 1) (r : ℂ)‖ = 2 * ‖(r : ℂ)‖ := by
  exact ⟨slitMap_centeredExteriorUnivalent 1 (by norm_num),
    slitMap_one_actualHarmonic_norm_eq_two_norm hr0 hr1⟩
end SpringerLean