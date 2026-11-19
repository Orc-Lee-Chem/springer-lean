import Mathlib.Analysis.Convex.Function
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace SpringerLean
set_option Elab.async false

noncomputable def convexGridKnot (a h : ℝ) (i : ℕ) : ℝ := a+(i : ℝ)*h
noncomputable def convexGridSlope (v : ℕ → ℝ) (h : ℝ) (i : ℕ) : ℝ :=
  (v (i+1)-v i)/h
noncomputable def convexGridWeight (v : ℕ → ℝ) (h : ℝ) (i : ℕ) : ℝ :=
  convexGridSlope v h (i+1)-convexGridSlope v h i

noncomputable def convexGridAffinePrefix
    (v : ℕ → ℝ) (a h : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  v 0+convexGridSlope v h 0*(x-a)+
    ∑ j ∈ Finset.range N, convexGridWeight v h j*(x-convexGridKnot a h (j+1))

noncomputable def convexGridHinge
    (v : ℕ → ℝ) (a h : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  v 0+convexGridSlope v h 0*(x-a)+
    ∑ j ∈ Finset.range N,
      convexGridWeight v h j*max (x-convexGridKnot a h (j+1)) 0

/-- Algebraic telescoping of adjacent secant slopes. This does not assume
convexity; convexity will make the resulting hinge weights nonnegative. -/
theorem convexGridAffinePrefix_eq
    (v : ℕ → ℝ) (a h : ℝ) (hh : h ≠ 0) (N : ℕ) (x : ℝ) :
    convexGridAffinePrefix v a h N x =
      v N+convexGridSlope v h N*(x-convexGridKnot a h N) := by
  induction N with
  | zero => simp [convexGridAffinePrefix,convexGridKnot]
  | succ N ih =>
      have hstep : convexGridAffinePrefix v a h (N+1) x =
          convexGridAffinePrefix v a h N x+
            convexGridWeight v h N*(x-convexGridKnot a h (N+1)) := by
        simp only [convexGridAffinePrefix,Finset.sum_range_succ]
        ring
      rw [hstep,ih]
      dsimp only [convexGridWeight,convexGridSlope,convexGridKnot]
      push_cast
      field_simp [hh]
      <;> ring

theorem convexGridWeight_nonneg
    (v : ℕ → ℝ) {h : ℝ} (hh : 0 < h) (i : ℕ)
    (hmid : v (i+1) ≤ (v i+v (i+2))/2) :
    0 ≤ convexGridWeight v h i := by
  have he : convexGridWeight v h i =
      (v (i+2)-2*v (i+1)+v i)/h := by
    dsimp only [convexGridWeight,convexGridSlope]
    ring
  rw [he]
  apply div_nonneg _ hh.le
  linarith

/-- Finite interval coverage avoids choosing a floor at a grid endpoint. -/
theorem convexGrid_cell_exists (a h : ℝ) (N : ℕ) (x : ℝ)
    (ha : a ≤ x) (hb : x ≤ convexGridKnot a h (N+1)) :
    ∃ i : ℕ, i ≤ N ∧ convexGridKnot a h i ≤ x ∧
      x ≤ convexGridKnot a h (i+1) := by
  induction N with
  | zero => exact ⟨0,le_rfl,by simpa [convexGridKnot] using ha,hb⟩
  | succ N ih =>
      by_cases hx : x ≤ convexGridKnot a h (N+1)
      · obtain ⟨i,hi,hlo,hhi⟩ := ih hx
        exact ⟨i,by omega,hlo,hhi⟩
      · exact ⟨N+1,le_rfl,(le_of_not_ge hx),hb⟩

end SpringerLean
