import Mathlib.Tactic

namespace SpringerLean

/-- The model Jacobian denominator is at least one throughout the
active radial-deficit range.  Clearing `4-e` leaves the short factor
`5e(4-2e-5e²)`. -/
theorem coarseJacobian_denominator_ge_one
    {e : ℝ} (he0 : 0 ≤ e) (heδ : e ≤ 1/20) :
    1 ≤ (1+5*e)*(1-5*e^2/(4-e)) := by
  have hden : 0 < 4-e := by linarith
  have he2 : e^2 ≤ e/20 := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr heδ)]
  have hpoly : 0 ≤ 4-2*e-5*e^2 := by nlinarith [he2]
  have hprod : 0 ≤ 5*e*(4-2*e-5*e^2) := by positivity
  have hid : (1+5*e)*(1-5*e^2/(4-e)) =
      (1+5*e)*(4-e-5*e^2)/(4-e) := by
    field_simp
  rw [hid]
  apply (le_div_iff₀ hden).2
  nlinarith [hprod]

/-- The exact Jacobian is bounded by a linear factor; `1+12e` is an
available looser bound for subsequent integral estimates. -/
theorem coarseJacobian_le_twelve
    {e : ℝ} (he0 : 0 ≤ e) (heδ : e ≤ 1/20) :
    (1+10*e) /
      Real.sqrt ((1+5*e)*(1-5*e^2/(4-e))) ≤ 1+12*e := by
  have hd := coarseJacobian_denominator_ge_one he0 heδ
  have hs : 1 ≤ Real.sqrt ((1+5*e)*(1-5*e^2/(4-e))) := by
    simpa using Real.sqrt_le_sqrt hd
  have hspos : 0 < Real.sqrt ((1+5*e)*(1-5*e^2/(4-e))) := by linarith
  apply (div_le_iff₀ hspos).2
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1+10*e)
    (by linarith : 0 ≤ Real.sqrt ((1+5*e)*(1-5*e^2/(4-e)))-1)]

/-- On the active positive arc, the radial deficit is controlled by
the square of the sine with the exact factor `80/79`. -/
theorem coarseRadialDeficit_le_sineSquare
    {c : ℝ} (hc0 : 39/40 ≤ c) (hc1 : c ≤ 1) :
    2*(1-c) ≤ (80/79 : ℝ)*(1-c^2) := by
  have hprod : 0 ≤ (1-c)*(c-39/40) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hprod]

end SpringerLean

#print axioms SpringerLean.coarseJacobian_denominator_ge_one
#print axioms SpringerLean.coarseJacobian_le_twelve
#print axioms SpringerLean.coarseRadialDeficit_le_sineSquare
