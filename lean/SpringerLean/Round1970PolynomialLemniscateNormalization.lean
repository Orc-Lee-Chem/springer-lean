import SpringerLean.Round1969PolynomialAffineMonic

open Polynomial Set

namespace SpringerLean

/-- Exact unit-lemniscate relation under monic affine normalization.
The threshold on the original polynomial is the norm of the new
leading coefficient before division. -/
theorem polynomialAffineMonic_unit_sublevel_iff
    (P : ℂ[X]) (hP : 0 < P.natDegree)
    (c : ℂ) (r : ℝ) (hr : r ≠ 0) (z : ℂ) :
    ‖(polynomialAffineMonic P c r).eval z‖ ≤ 1 ↔
      ‖P.eval (c + (r : ℂ) * z)‖ ≤
        ‖P.leadingCoeff * (r : ℂ) ^ P.natDegree‖ := by
  have hPzero : P ≠ 0 := by
    intro hzero
    simp [hzero] at hP
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hden : 0 < ‖P.leadingCoeff * (r : ℂ) ^ P.natDegree‖ := by
    apply norm_pos_iff.mpr
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hPzero)
      (pow_ne_zero _ hrc)
  rw [polynomialAffineMonic_eval P c r hr z, norm_div]
  exact (div_le_iff₀ hden).trans (by simp)

/-- The monic affine normalization preserves the connectedness of the
actual sublevel lemniscate at its corresponding threshold. -/
theorem polynomialAffineMonic_unit_lemniscate_connected
    (P : ℂ[X]) (hP : 0 < P.natDegree)
    (c : ℂ) (r : ℝ) (hr : r ≠ 0)
    (hK : IsConnected
      {w : ℂ | ‖P.eval w‖ ≤
        ‖P.leadingCoeff * (r : ℂ) ^ P.natDegree‖}) :
    IsConnected {z : ℂ | ‖(polynomialAffineMonic P c r).eval z‖ ≤ 1} := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  let g : ℂ → ℂ := fun w => (w - c) / (r : ℂ)
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hset : g ''
      {w : ℂ | ‖P.eval w‖ ≤
        ‖P.leadingCoeff * (r : ℂ) ^ P.natDegree‖} =
      {z : ℂ | ‖(polynomialAffineMonic P c r).eval z‖ ≤ 1} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have heq : c + (r : ℂ) * g w = w := by
        dsimp [g]
        field_simp [hrc]
        ring
      apply (polynomialAffineMonic_unit_sublevel_iff P hP c r hr (g w)).2
      rw [heq]
      exact hw
    · intro hz
      refine ⟨c + (r : ℂ) * z, ?_, ?_⟩
      · exact (polynomialAffineMonic_unit_sublevel_iff P hP c r hr z).1 hz
      · dsimp [g]
        field_simp [hrc]
        ring
  rw [← hset]
  exact hK.image g hg.continuousOn

end SpringerLean

#print axioms SpringerLean.polynomialAffineMonic_unit_sublevel_iff
#print axioms SpringerLean.polynomialAffineMonic_unit_lemniscate_connected
