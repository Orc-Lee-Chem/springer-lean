import SpringerLean.Round1484ActualTwoFineWidths

namespace SpringerLean

/-- The elementary cutoff budget used by both later phase branches.
The width input is the already proved disk-scale deficit, and the
cutoff is truncated at one fifth of the disk exponent. -/
theorem largePhase_cutoff_budget
    (m n : ℕ) (hm : 1500 ≤ m) (hmn : m < n)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < 1)
    (hlog : (n:ℝ)*d*Real.log (2/d)<3/2) :
    let y : ℝ := (m:ℝ)*d*Real.log (2/d)/3
    let a : ℝ := min (3/y) ((m:ℝ)/5)
    0 < y ∧ y < 1/2 ∧ 6 < a ∧ a*y ≤ 3 := by
  let L : ℝ := Real.log (2/d)
  let y : ℝ := (m:ℝ)*d*L/3
  let a : ℝ := min (3/y) ((m:ℝ)/5)
  have hL : 0 < L := by
    apply Real.log_pos
    apply (one_lt_div hd0).2
    linarith
  have hm0 : (0:ℝ)<m := by
    exact_mod_cast (by omega : 0<m)
  have hmnR : ((m:ℝ)<(n:ℝ)) := by exact_mod_cast hmn
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hyhalf : y < 1/2 := by
    have hmul := mul_le_mul_of_nonneg_right hmnR.le (mul_nonneg hd0.le hL.le)
    dsimp [y]
    nlinarith [hmul,hlog]
  have ha1 : 6 < 3/y := by
    apply (lt_div_iff₀ hy0).2
    linarith
  have ha2 : 6 < (m:ℝ)/5 := by
    have hmR : (1500:ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have ha : 6 < a := lt_min ha1 ha2
  have hay : a*y ≤ 3 := by
    have hle : a ≤ 3/y := min_le_left _ _
    have hmul := mul_le_mul_of_nonneg_right hle hy0.le
    have hcancel : (3/y)*y=3 := by field_simp
    nlinarith
  exact ⟨hy0,hyhalf,ha,hay⟩

end SpringerLean

#print axioms SpringerLean.largePhase_cutoff_budget
