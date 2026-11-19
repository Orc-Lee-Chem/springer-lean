import Mathlib.Tactic

namespace SpringerLean

/-- The two-point near/far alternative through deficit 1/10. The
rational 451/100 leaves a strict margin at the endpoint. -/
theorem twoPoint_near_far_451_100
    {u e : ℝ} (he0 : 0 ≤ e) (heδ : e ≤ 1/10)
    (_hu0 : 0 ≤ u) (_hu4 : u ≤ 4)
    (hpair : u*(4-u) ≤ 16*e) :
    u ≤ (451/100 : ℝ)*e ∨ 4-u ≤ (451/100 : ℝ)*e := by
  by_contra h
  push_neg at h
  have hquad : e^2 ≤ e/10 := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr heδ)]
  have hprod : 0 <
      (u-(451/100 : ℝ)*e)*(4-(451/100 : ℝ)*e-u) :=
    mul_pos (by linarith [h.1]) (by linarith [h.2])
  have hbase : 16*e ≤
      ((451/100 : ℝ)*e)*(4-(451/100 : ℝ)*e) := by
    nlinarith [hquad]
  nlinarith [hprod]

/-- The forward half excludes the far alternative already at deficit
1/10, since its chord square is at most eight. -/
theorem twoPoint_forward_half_near_451_100
    {u e : ℝ} (he0 : 0 ≤ e) (heδ : e ≤ 1/10)
    (hu0 : 0 ≤ u) (hu4 : u ≤ 4)
    (hpair : u*(4-u) ≤ 16*e)
    (hforward : u^2 ≤ 8) :
    u ≤ (451/100 : ℝ)*e := by
  rcases twoPoint_near_far_451_100 he0 heδ hu0 hu4 hpair with hnear | hfar
  · exact hnear
  · have hlarge : (3549/1000 : ℝ) ≤ u := by linarith
    nlinarith [sq_nonneg (u-3549/1000)]

/-- A chord whose square is controlled by both points' far-side
two-point bounds must take the near alternative on the 1/10 range. -/
theorem twoPoint_second_near_of_sq_451_100
    {u e : ℝ} (he0 : 0 ≤ e) (heδ : e ≤ 1/10)
    (hu0 : 0 ≤ u) (hu4 : u ≤ 4)
    (hpair : u*(4-u) ≤ 16*e)
    (hsq : u^2 ≤ 16*(451/100 : ℝ)*e) :
    u ≤ (451/100 : ℝ)*e := by
  rcases twoPoint_near_far_451_100 he0 heδ hu0 hu4 hpair with hnear | hfar
  · exact hnear
  · have hlarge : (3549/1000 : ℝ) ≤ u := by linarith
    nlinarith [sq_nonneg (u-3549/1000)]

end SpringerLean

#print axioms SpringerLean.twoPoint_near_far_451_100
#print axioms SpringerLean.twoPoint_forward_half_near_451_100
#print axioms SpringerLean.twoPoint_second_near_of_sq_451_100
