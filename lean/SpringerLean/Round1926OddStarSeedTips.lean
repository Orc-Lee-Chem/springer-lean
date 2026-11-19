import SpringerLean.Round1925OddStarSeedGeometry

namespace SpringerLean

theorem oddStarSeed_sqrt_pos (t : ℝ) (ht : |t| < 1) :
    0 < Real.sqrt (1 - t ^ 2) := by
  apply Real.sqrt_pos.2
  rcases abs_lt.mp ht with ⟨hl, hu⟩
  nlinarith

/-- Both distinguished preimages of the seed map lie on the unit circle. -/
theorem oddStarSeed_tip_norms (t : ℝ) (ht : |t| < 1) :
    let s := Real.sqrt (1 - t ^ 2)
    ‖(t : ℂ) * Complex.I - s‖ = 1 ∧
      ‖(t : ℂ) * Complex.I + s‖ = 1 := by
  let s := Real.sqrt (1 - t ^ 2)
  have hs : s ^ 2 = 1 - t ^ 2 :=
    Real.sq_sqrt (le_of_lt (by
      rcases abs_lt.mp ht with ⟨hl, hu⟩
      nlinarith))
  constructor
  · have hsq : ‖(t : ℂ) * Complex.I - s‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
      nlinarith [hs]
    nlinarith [norm_nonneg ((t : ℂ) * Complex.I - s)]
  · have hsq : ‖(t : ℂ) * Complex.I + s‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
      nlinarith [hs]
    nlinarith [norm_nonneg ((t : ℂ) * Complex.I + s)]

/-- The two tip values needed to identify the odd-star perturbation. -/
theorem oddStarSeed_tip_values (t : ℝ) (ht : |t| < 1) :
    let s := Real.sqrt (1 - t ^ 2)
    oddStarSeed t ((t : ℂ) * Complex.I - s) = 0 ∧
      oddStarSeed t ((t : ℂ) * Complex.I + s) = (4 * s : ℝ) := by
  let s := Real.sqrt (1 - t ^ 2)
  have hs : s ≠ 0 := (oddStarSeed_sqrt_pos t ht).ne'
  constructor
  · simp [oddStarSeed, s]
  · change (((t : ℂ) * Complex.I + s - (t : ℂ) * Complex.I + s) ^ 2 /
        ((t : ℂ) * Complex.I + s - (t : ℂ) * Complex.I)) = (4 * s : ℝ)
    have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs
    field_simp [hsc]
    push_cast
    ring

end SpringerLean

#print axioms SpringerLean.oddStarSeed_tip_norms
#print axioms SpringerLean.oddStarSeed_tip_values
