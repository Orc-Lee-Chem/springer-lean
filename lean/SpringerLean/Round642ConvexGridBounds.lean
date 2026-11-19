import SpringerLean.Round641ConvexGridCells

namespace SpringerLean
set_option Elab.async false

theorem convexGridWeight_nonneg_of_convex
    (ψ : ℝ → ℝ) (hψ : ConvexOn ℝ Set.univ ψ)
    (a : ℝ) {h : ℝ} (hh : 0 < h) (i : ℕ) :
    0 ≤ convexGridWeight (fun j => ψ (convexGridKnot a h j)) h i := by
  apply convexGridWeight_nonneg _ hh
  have hmid := hψ.2
    (show convexGridKnot a h i ∈ Set.univ from Set.mem_univ _)
    (show convexGridKnot a h (i+2) ∈ Set.univ from Set.mem_univ _)
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (1/2 : ℝ)+1/2=1 by norm_num)
  have hp : (1/2 : ℝ)*convexGridKnot a h i+
      (1/2 : ℝ)*convexGridKnot a h (i+2) = convexGridKnot a h (i+1) := by
    dsimp only [convexGridKnot]
    push_cast
    ring
  simp only [smul_eq_mul,hp] at hmid
  convert hmid using 1 <;> ring

/-- The finite hinge interpolant lies above the original convex function. -/
theorem convexGridHinge_ge_of_convex
    (ψ : ℝ → ℝ) (hψ : ConvexOn ℝ Set.univ ψ)
    (a : ℝ) {h : ℝ} (hh : 0 < h)
    {N i : ℕ} (hi : i ≤ N) {x : ℝ}
    (hlo : convexGridKnot a h i ≤ x)
    (hhi : x ≤ convexGridKnot a h (i+1)) :
    ψ x ≤ convexGridHinge (fun j => ψ (convexGridKnot a h j)) a h N x := by
  let t := (x-convexGridKnot a h i)/h
  have ht := convexGrid_cell_fraction_mem_unit a hh i hlo hhi
  have hpoint : (1-t)*convexGridKnot a h i+
      t*convexGridKnot a h (i+1) = x := by
    dsimp only [t,convexGridKnot]
    push_cast
    field_simp [hh.ne']
    <;> ring
  have hc := hψ.2
    (show convexGridKnot a h i ∈ Set.univ from Set.mem_univ _)
    (show convexGridKnot a h (i+1) ∈ Set.univ from Set.mem_univ _)
    (show (0 : ℝ) ≤ 1-t by dsimp only [t]; linarith [ht.2])
    (show (0 : ℝ) ≤ t from ht.1) (show 1-t+t=1 by ring)
  simp only [smul_eq_mul,hpoint] at hc
  rw [convexGridHinge_eq_chord _ a hh hi hlo hhi]
  exact hc

theorem convexGridHinge_le_of_cell_values
    (v : ℕ → ℝ) (a : ℝ) {h : ℝ} (hh : 0 < h)
    {N i : ℕ} (hi : i ≤ N) {x u : ℝ}
    (hlo : convexGridKnot a h i ≤ x)
    (hhi : x ≤ convexGridKnot a h (i+1))
    (hvi : v i ≤ u) (hvi1 : v (i+1) ≤ u) :
    convexGridHinge v a h N x ≤ u := by
  rw [convexGridHinge_eq_chord v a hh hi hlo hhi]
  let t := (x-convexGridKnot a h i)/h
  have ht := convexGrid_cell_fraction_mem_unit a hh i hlo hhi
  have h0 : 0 ≤ 1-t := by dsimp only [t]; linarith [ht.2]
  calc
    _ ≤ (1-t)*u+t*u := add_le_add
      (mul_le_mul_of_nonneg_left hvi h0)
      (mul_le_mul_of_nonneg_left hvi1 ht.1)
    _ = u := by ring

end SpringerLean
