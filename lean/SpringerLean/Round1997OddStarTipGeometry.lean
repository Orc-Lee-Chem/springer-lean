import SpringerLean.Round1996OddStarOrdinaryPotential

namespace SpringerLean

/-- The fixed opposite-tip angle in every odd-order variation has a
strictly positive sine, negative cosine, and a denominator separated
from zero by the squared tip radius. -/
theorem oddStar_opposite_tip_angle_geometry
    (m : ℕ) (hm : 3 ≤ m) (r R : ℝ)
    (hr : 0 ≤ r) (hR : 0 ≤ R) :
    0 < Real.sin (Real.pi - Real.pi / (m : ℝ)) ∧
      Real.cos (Real.pi - Real.pi / (m : ℝ)) < 0 ∧
      R ^ 2 ≤ r ^ 2 + R ^ 2 -
        2 * r * R * Real.cos (Real.pi - Real.pi / (m : ℝ)) := by
  have hmreal : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hsmall : 0 < Real.pi / (m : ℝ) ∧
      Real.pi / (m : ℝ) < Real.pi / 2 := by
    constructor
    · positivity
    · apply (div_lt_div_iff₀ hmpos (by norm_num : (0 : ℝ) < 2)).2
      nlinarith [mul_pos Real.pi_pos (by linarith : (0 : ℝ) < (m : ℝ) - 2)]
  have hsin : 0 < Real.sin (Real.pi - Real.pi / (m : ℝ)) := by
    rw [Real.sin_pi_sub]
    exact Real.sin_pos_of_pos_of_lt_pi hsmall.1 (by linarith [Real.pi_pos])
  have hcos : Real.cos (Real.pi - Real.pi / (m : ℝ)) < 0 := by
    rw [Real.cos_pi_sub]
    have hcp : 0 < Real.cos (Real.pi / (m : ℝ)) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hsmall.2⟩
    linarith
  refine ⟨hsin, hcos, ?_⟩
  nlinarith [sq_nonneg r, mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr) hR]

end SpringerLean

#print axioms SpringerLean.oddStar_opposite_tip_angle_geometry
