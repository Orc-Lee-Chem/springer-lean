import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Tactic

open Finset

namespace SpringerLean

/-- The coefficient of the cell above the horizontal edge at `(i,j)`,
obtained by summing the horizontal edge coefficients in the column. -/
def gridCellWeight {A : Type*} [AddCommGroup A]
    (H : ℕ → ℕ → A) (i j : ℕ) : A :=
  ∑ t ∈ range (j+1), H i t

theorem gridCellWeight_base {A : Type*} [AddCommGroup A] (H : ℕ → ℕ → A) (i : ℕ) :
    gridCellWeight H i 0 = H i 0 := by simp [gridCellWeight]

theorem gridCellWeight_horizontal
    {A : Type*} [AddCommGroup A] (H : ℕ → ℕ → A) (i j : ℕ) :
    gridCellWeight H i (j+1) - gridCellWeight H i j = H i (j+1) := by
  simp [gridCellWeight,sum_range_succ]

theorem gridCellWeight_vertical
    {A : Type*} [AddCommGroup A] (H V : ℕ → ℕ → A)
    (hbase : ∀ i, H i 0 = H (i+1) 0 + V (i+1) 0)
    (hbalance : ∀ i j, H i (j+1) + V (i+1) j = H (i+1) (j+1) + V (i+1) (j+1))
    (i j : ℕ) :
    gridCellWeight H i j - gridCellWeight H (i+1) j = V (i+1) j := by
  induction j with
  | zero => rw [gridCellWeight_base,gridCellWeight_base,hbase i,add_sub_cancel_left]
  | succ j ih =>
    have h₁ := gridCellWeight_horizontal H i j
    have h₂ := gridCellWeight_horizontal H (i+1) j
    calc
      gridCellWeight H i (j+1) - gridCellWeight H (i+1) (j+1) =
          (gridCellWeight H i (j+1) - gridCellWeight H i j) -
          (gridCellWeight H (i+1) (j+1) - gridCellWeight H (i+1) j) +
          (gridCellWeight H i j - gridCellWeight H (i+1) j) := by abel
      _ = H i (j+1) + V (i+1) j - H (i+1) (j+1) := by rw [h₁,h₂,ih]; abel
      _ = V (i+1) (j+1) := by rw [hbalance,add_sub_cancel_left]

theorem gridCellWeight_eq_zero_of_column_eq_zero
    {A : Type*} [AddCommGroup A] (H : ℕ → ℕ → A) (i j : ℕ) (h : ∀ t, H i t = 0) :
    gridCellWeight H i j = 0 := by simp [gridCellWeight,h]

/-- The cell weights of a finite closed grid chain vanish beyond the
row bound and the column bound. The leftmost column is kept free of
horizontal edges by translating the grid. -/
theorem gridCellWeight_support
    {A : Type*} [AddCommGroup A] (H V : ℕ → ℕ → A) (N : ℕ)
    (hbase : ∀ i, H i 0 = H (i+1) 0 + V (i+1) 0)
    (hbalance : ∀ i j, H i (j+1) + V (i+1) j = H (i+1) (j+1) + V (i+1) (j+1))
    (hleft : ∀ j, H 0 j = 0)
    (htop : ∀ i j, N ≤ j → V i j = 0)
    (hright : ∀ i j, N ≤ i → H i j = 0)
    (i j : ℕ) (hij : N ≤ i ∨ N ≤ j) : gridCellWeight H i j = 0 := by
  rcases hij with hi | hj
  · exact gridCellWeight_eq_zero_of_column_eq_zero H i j (fun t => hright i t hi)
  · induction i with
    | zero => exact gridCellWeight_eq_zero_of_column_eq_zero H 0 j hleft
    | succ i ih =>
      have h := gridCellWeight_vertical H V hbase hbalance i j
      rw [ih,htop _ _ hj,zero_sub,neg_eq_zero] at h
      exact h

end SpringerLean
