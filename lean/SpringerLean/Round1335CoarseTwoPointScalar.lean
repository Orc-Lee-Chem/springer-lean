import Mathlib.Tactic

namespace SpringerLean

/-- At radial deficit at most `1/20`, the two-point inequality has a
uniform `17e/4` near/far dichotomy.  This version avoids square roots. -/
theorem twoPoint_near_far_17_4
    {u e : ℝ} (he0 : 0 ≤ e) (heδ : e ≤ 1/20)
    (_hu0 : 0 ≤ u) (_hu4 : u ≤ 4)
    (hpair : u * (4 - u) ≤ 16 * e) :
    u ≤ (17/4 : ℝ) * e ∨ 4 - u ≤ (17/4 : ℝ) * e := by
  by_contra h
  push Not at h
  have hquad : e ^ 2 ≤ e / 20 := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr heδ)]
  have hprod : 0 <
      (u - (17/4 : ℝ) * e) * (4 - (17/4 : ℝ) * e - u) :=
    mul_pos (by linarith [h.1]) (by linarith [h.2])
  have hbase : 16 * e ≤
      ((17/4 : ℝ) * e) * (4 - (17/4 : ℝ) * e) := by
    nlinarith [hquad]
  nlinarith [hprod]

/-- A point in the forward half-plane cannot take the far branch:
`(4-17/80)^2>8`. -/
theorem twoPoint_forward_half_near_17_4
    {u e : ℝ} (he0 : 0 ≤ e) (heδ : e ≤ 1/20)
    (hu0 : 0 ≤ u) (hu4 : u ≤ 4)
    (hpair : u * (4 - u) ≤ 16 * e)
    (hforward : u ^ 2 ≤ 8) :
    u ≤ (17/4 : ℝ) * e := by
  rcases twoPoint_near_far_17_4 he0 heδ hu0 hu4 hpair with hnear | hfar
  · exact hnear
  · have hlarge : (303/80 : ℝ) ≤ u := by linarith
    nlinarith [sq_nonneg (u - 303/80)]

/-- The cosine-rule algebra that turns a near chord into a quadratic
projection deficit.  Here `R` is the endpoint radius, `2-e` the
compared radius, and `x` its projection onto the endpoint direction. -/
theorem nearChord_projection_deficit_five
    {R e u x : ℝ}
    (hR : 39/20 ≤ R) (he0 : 0 ≤ e) (heδ : e ≤ 1/20)
    (hu0 : 0 ≤ u) (hnear : u ≤ (17/4 : ℝ) * e)
    (hcos : u ^ 2 = R ^ 2 + (2 - e) ^ 2 - 2 * R * x)
    (hrle : 2 - e ≤ R) :
    2 - x ≤ e + 5 * e ^ 2 := by
  have hRpos : 0 < R := by linarith
  have hquad : e ^ 2 ≤ e / 20 := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr heδ)]
  have hu2 : u ^ 2 ≤ (17/4 * e) ^ 2 := by
    nlinarith [sq_nonneg ((17/4 : ℝ) * e - u)]
  have hgap : 0 ≤ R - (2 - e) := by linarith
  have hdiff : u ^ 2 - (R - (2 - e)) ^ 2 =
      2 * R * ((2 - e) - x) := by nlinarith [hcos]
  have hcost : u ^ 2 ≤ 10 * R * e ^ 2 := by
    have hE2 : 0 ≤ e ^ 2 := sq_nonneg e
    nlinarith [mul_nonneg (show 0 ≤ R - 39/20 by linarith) hE2]
  have hnon : 0 ≤ (R - (2 - e)) ^ 2 := sq_nonneg _
  nlinarith [hcost, hdiff, hnon]

end SpringerLean

#print axioms SpringerLean.twoPoint_near_far_17_4
#print axioms SpringerLean.twoPoint_forward_half_near_17_4
#print axioms SpringerLean.nearChord_projection_deficit_five
