import SpringerLean.Round29PotentialDiffFar

namespace SpringerLean

/-- The radial reference potential for the compensated far field. -/
noncomputable def radialReferencePotential (z : ℂ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (1 + ‖z‖ ^ 2)

/-- At nonzero targets the reference differs from log‖z‖ by at most a
quadratic reciprocal error. -/
theorem radialReferencePotential_sub_log_norm_bound
    (z : ℂ) (hz : z ≠ 0) :
    0 ≤ radialReferencePotential z - Real.log ‖z‖ ∧
    radialReferencePotential z - Real.log ‖z‖ ≤
      (1 / 2 : ℝ) / ‖z‖ ^ 2 := by
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hsq : 0 < ‖z‖ ^ 2 := pow_pos hnorm _
  have hne : ‖z‖ ^ 2 ≠ 0 := ne_of_gt hsq
  have hratio : 0 ≤ 1 / ‖z‖ ^ 2 := by positivity
  have hfact : 1 + ‖z‖ ^ 2 = ‖z‖ ^ 2 * (1 + 1 / ‖z‖ ^ 2) := by
    field_simp
    ring
  have hlog : radialReferencePotential z - Real.log ‖z‖ =
      (1 / 2 : ℝ) * Real.log (1 + 1 / ‖z‖ ^ 2) := by
    dsimp [radialReferencePotential]
    rw [hfact, Real.log_mul hne (by positivity : 1 + 1 / ‖z‖ ^ 2 ≠ 0)]
    rw [Real.log_pow]
    ring
  rw [hlog]
  constructor
  · apply mul_nonneg (by norm_num)
    exact Real.log_nonneg (by linarith)
  · have hb := Real.log_le_sub_one_of_pos
      (by linarith : 0 < 1 + 1 / ‖z‖ ^ 2)
    have hmul : (1 / 2 : ℝ) / ‖z‖ ^ 2 = (1 / 2 : ℝ) * (1 / ‖z‖ ^ 2) := by ring
    rw [hmul]
    exact mul_le_mul_of_nonneg_left (by linarith [hb]) (by norm_num)
end SpringerLean