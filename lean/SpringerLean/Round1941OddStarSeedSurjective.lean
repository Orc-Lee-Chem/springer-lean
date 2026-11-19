import SpringerLean.Round1940OddStarSeedBoundary
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace SpringerLean

/-- Every complex target has a preimage under the rational seed, away from
its removable pole. The two roots of the displayed quadratic are used in
the next round to locate the omitted boundary precisely. -/
theorem oddStarSeed_exists_preimage
    (t : ℝ) (ht : |t| < 1) (w : ℂ) :
    ∃ z : ℂ, z ≠ (t : ℂ) * Complex.I ∧ oddStarSeed t z = w := by
  let s : ℝ := Real.sqrt (1 - t ^ 2)
  have hspos : 0 < s := oddStarSeed_sqrt_pos t ht
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
  obtain ⟨h, hh⟩ :=
    IsAlgClosed.exists_pow_nat_eq (w * (w - 4 * (s : ℂ))) (by norm_num : 0 < 2)
  let u : ℂ := (w - 2 * (s : ℂ) + h) / 2
  have hquad : u ^ 2 + (2 * (s : ℂ) - w) * u + (s : ℂ) ^ 2 = 0 := by
    calc
      u ^ 2 + (2 * (s : ℂ) - w) * u + (s : ℂ) ^ 2 =
          (h ^ 2 - w * (w - 4 * (s : ℂ))) / 4 := by
            dsimp [u]
            ring
      _ = 0 := by rw [hh]; ring
  have hu : u ≠ 0 := by
    intro h0
    rw [h0] at hquad
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      zero_add, zero_add] at hquad
    exact hsc (sq_eq_zero_iff.mp hquad)
  refine ⟨u + (t : ℂ) * Complex.I, ?_, ?_⟩
  · intro h0
    apply hu
    linear_combination h0
  · unfold oddStarSeed
    simp only [add_sub_cancel_right]
    change (u + (s : ℂ)) ^ 2 / u = w
    apply (div_eq_iff hu).mpr
    linear_combination hquad

end SpringerLean

#print axioms SpringerLean.oddStarSeed_exists_preimage
