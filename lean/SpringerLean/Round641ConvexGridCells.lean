import SpringerLean.Round630ConvexGridAlgebra

namespace SpringerLean
set_option Elab.async false

theorem convexGridKnot_mono (a : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    Monotone (convexGridKnot a h) := by
  intro i j hij
  dsimp only [convexGridKnot]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (show (i : ℝ) ≤ (j : ℝ) by exact_mod_cast hij) hh)

/-- On each grid cell the finite hinge expression is the corresponding
affine interpolant; all later hinges vanish there. -/
theorem convexGridHinge_eq_cell
    (v : ℕ → ℝ) (a : ℝ) {h : ℝ} (hh : 0 < h)
    {N i : ℕ} (hi : i ≤ N) {x : ℝ}
    (hlo : convexGridKnot a h i ≤ x)
    (hhi : x ≤ convexGridKnot a h (i+1)) :
    convexGridHinge v a h N x =
      v i+convexGridSlope v h i*(x-convexGridKnot a h i) := by
  classical
  have hmono := convexGridKnot_mono a hh.le
  have hsub : Finset.range i ⊆ Finset.range N := Finset.range_mono hi
  have hzero (j : ℕ) (hj : j ∈ Finset.range N) (hjn : j ∉ Finset.range i) :
      convexGridWeight v h j*max (x-convexGridKnot a h (j+1)) 0 = 0 := by
    have hij : i ≤ j := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hjn)
    have hx : x ≤ convexGridKnot a h (j+1) :=
      hhi.trans (hmono (Nat.add_le_add_right hij 1))
    rw [max_eq_right (sub_nonpos.mpr hx),mul_zero]
  have hsum : (∑ j ∈ Finset.range N,
      convexGridWeight v h j*max (x-convexGridKnot a h (j+1)) 0) =
      ∑ j ∈ Finset.range i,
        convexGridWeight v h j*(x-convexGridKnot a h (j+1)) := by
    calc
      _ = ∑ j ∈ Finset.range i,
          convexGridWeight v h j*max (x-convexGridKnot a h (j+1)) 0 :=
        (Finset.sum_subset hsub hzero).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j+1 ≤ i := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
        have hx := (hmono hji).trans hlo
        rw [max_eq_left (sub_nonneg.mpr hx)]
  have heq : convexGridHinge v a h N x = convexGridAffinePrefix v a h i x := by
    simpa only [convexGridHinge,convexGridAffinePrefix] using
      congrArg (fun y => v 0+convexGridSlope v h 0*(x-a)+y) hsum
  rw [heq,convexGridAffinePrefix_eq v a h hh.ne' i x]

theorem convexGridHinge_eq_chord
    (v : ℕ → ℝ) (a : ℝ) {h : ℝ} (hh : 0 < h)
    {N i : ℕ} (hi : i ≤ N) {x : ℝ}
    (hlo : convexGridKnot a h i ≤ x)
    (hhi : x ≤ convexGridKnot a h (i+1)) :
    convexGridHinge v a h N x =
      (1-(x-convexGridKnot a h i)/h)*v i+
        ((x-convexGridKnot a h i)/h)*v (i+1) := by
  rw [convexGridHinge_eq_cell v a hh hi hlo hhi]
  dsimp only [convexGridSlope]
  ring

theorem convexGrid_cell_fraction_mem_unit
    (a : ℝ) {h : ℝ} (hh : 0 < h) (i : ℕ) {x : ℝ}
    (hlo : convexGridKnot a h i ≤ x)
    (hhi : x ≤ convexGridKnot a h (i+1)) :
    0 ≤ (x-convexGridKnot a h i)/h ∧
      (x-convexGridKnot a h i)/h ≤ 1 := by
  refine ⟨div_nonneg (sub_nonneg.mpr hlo) hh.le,?_⟩
  apply (div_le_one hh).mpr
  dsimp only [convexGridKnot] at *
  push_cast at hhi
  linarith

end SpringerLean
