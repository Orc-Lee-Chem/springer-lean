import SpringerLean.Round1526SmallCapAngle

namespace SpringerLean
set_option maxHeartbeats 320000

/-- The local algebraic identity that turns the central-arc cosine
defect into a Poisson mass and a constant. -/
theorem centeredPoisson_cosine_defect_identity
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    2*(1-Real.cos θ)*
        poissonKernel 0 (r:ℂ) (circleMap 0 1 θ) =
      (1-r^2)/r - (1-r)^2/r *
        poissonKernel 0 (r:ℂ) (circleMap 0 1 θ) := by
  rw [poissonKernel_centered_cosine_formula hr0.le hr1]
  have hcos : 0 ≤ 1-Real.cos θ := sub_nonneg.mpr (Real.cos_le_one θ)
  have hsq : 0 < (1-r)^2 := sq_pos_of_pos (sub_pos.mpr hr1)
  have hden : 0 < 1+r^2-2*r*Real.cos θ := by
    have hprod := mul_nonneg hr0.le hcos
    nlinarith only [hsq,hprod]
  let D : ℝ := 1+r^2-2*r*Real.cos θ
  have hDne : D ≠ 0 := ne_of_gt hden
  change 2*(1-Real.cos θ)*((1-r^2)/D) =
    (1-r^2)/r-(1-r)^2/r*((1-r^2)/D)
  field_simp [ne_of_gt hr0,hDne]
  dsimp [D]
  ring

end SpringerLean

#print axioms SpringerLean.centeredPoisson_cosine_defect_identity
