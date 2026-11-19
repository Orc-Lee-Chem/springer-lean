import SpringerLean.Round2144GridCycleWeights

open Finset

namespace SpringerLean

private theorem sum_grid_difference
    {A : Type*} [CommRing A] (u v : ℕ → A) (N : ℕ) :
    ∑ j ∈ range (N+1), u j * (v j - v (j+1)) =
      u 0 * v 0 + ∑ j ∈ range N, (u (j+1) - u j) * v (j+1) - u N * v (N+1) := by
  induction N with
  | zero => simp [mul_sub]
  | succ N ih =>
    rw [sum_range_succ _ (N+1),ih,sum_range_succ _ N]
    ring

/-- Pair a closed grid chain with arbitrary integrals on its oriented
edges. The result is the sum of the cell weights times the integrals
around the cells. -/
theorem gridCycle_pairing
    {A : Type*} [CommRing A] (H V L M : ℕ → ℕ → A) (N : ℕ)
    (hbase : ∀ i, H i 0 = H (i+1) 0 + V (i+1) 0)
    (hbalance : ∀ i j, H i (j+1) + V (i+1) j = H (i+1) (j+1) + V (i+1) (j+1))
    (hleft : ∀ j, H 0 j = 0) (hVleft : ∀ j, V 0 j = 0)
    (htop : ∀ i j, N ≤ j → V i j = 0)
    (hright : ∀ i j, N ≤ i → H i j = 0) :
    ∑ i ∈ range (N+1), ∑ j ∈ range (N+1),
        gridCellWeight H i j * (L i j + M (i+1) j - L i (j+1) - M i j) =
      ∑ i ∈ range (N+1), ∑ j ∈ range (N+1), (H i j * L i j + V i j * M i j) := by
  let W := gridCellWeight H
  have hW := gridCellWeight_support H V N hbase hbalance hleft htop hright
  have hH (i : ℕ) :
      ∑ j ∈ range (N+1), W i j * (L i j - L i (j+1)) =
      ∑ j ∈ range (N+1), H i j * L i j := by
    rw [sum_grid_difference]
    change gridCellWeight H i 0 * L i 0 +
      ∑ j ∈ range N, (gridCellWeight H i (j+1) - gridCellWeight H i j) * L i (j+1) -
      gridCellWeight H i N * L i (N+1) = _
    rw [hW i N (Or.inr le_rfl),zero_mul,sub_zero,gridCellWeight_base]
    simp only [gridCellWeight_horizontal]
    rw [sum_range_succ']
    exact add_comm _ _
  have hV (j : ℕ) :
      ∑ i ∈ range (N+1), W i j * (M (i+1) j - M i j) =
      ∑ i ∈ range (N+1), V i j * M i j := by
    have h := sum_grid_difference (fun i => W i j) (fun i => -M i j) N
    have hleftW : W 0 j = 0 := gridCellWeight_eq_zero_of_column_eq_zero H 0 j hleft
    have hV' (i : ℕ) : W (i+1) j - W i j = -V (i+1) j := by
      rw [←gridCellWeight_vertical H V hbase hbalance i j]
      abel
    have hrightW : W N j = 0 := hW N j (Or.inl le_rfl)
    simp only [neg_sub_neg,hleftW,hrightW,zero_mul,zero_add,sub_zero,
      hV',neg_mul_neg] at h
    rw [h,sum_range_succ',hVleft,zero_mul,add_zero]
  have he (i j : ℕ) :
      W i j * (L i j + M (i+1) j - L i (j+1) - M i j) =
        W i j * (L i j - L i (j+1)) + W i j * (M (i+1) j - M i j) := by ring
  change ∑ i ∈ range (N+1), ∑ j ∈ range (N+1),
    W i j * (L i j + M (i+1) j - L i (j+1) - M i j) = _
  have hVS : ∑ i ∈ range (N+1), ∑ j ∈ range (N+1),
      W i j * (M (i+1) j - M i j) =
    ∑ i ∈ range (N+1), ∑ j ∈ range (N+1), V i j * M i j := by
    calc
      _ = ∑ j ∈ range (N+1), ∑ i ∈ range (N+1), W i j * (M (i+1) j - M i j) := Finset.sum_comm
      _ = ∑ j ∈ range (N+1), ∑ i ∈ range (N+1), V i j * M i j := by simp only [hV]
      _ = _ := Finset.sum_comm
  simp only [he,sum_add_distrib,hH,hVS]

end SpringerLean
