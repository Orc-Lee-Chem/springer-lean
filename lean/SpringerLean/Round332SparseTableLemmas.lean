import SpringerLean.Round331SparseCoefficientCore
import Init.Data.List.Range

namespace SpringerLean.RatPolyCheck

theorem getD_map_range_le {α : Type _} (f : Nat → α) (fallback : α)
    (N n : Nat) (hn : n ≤ N) :
    ((List.range (N + 1)).map f).getD n fallback = f n := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (Nat.lt_succ_of_le hn)]
  rfl

theorem sparseSeriesMul_getD {σ : Type _} [DecidableEq σ]
    (r : σ → σ → Bool) (A B : List (Sparse σ)) (N n : Nat) (hn : n ≤ N) :
    (sparseSeriesMul r A B N).getD n [] = sparseCauchyCoeff r A B n :=
  getD_map_range_le _ _ N n hn

theorem sparseSeriesOne_getD {σ : Type _} (N n : Nat) (hn : n ≤ N) :
    (@sparseSeriesOne σ N).getD n [] = if n = 0 then [([], 1)] else [] :=
  getD_map_range_le _ _ N n hn

theorem phiSparseCoefficients_getD (N n : Nat) (hn : n ≤ N) :
    (SpringerLean.phiSparseCoefficients N).getD n [] =
      if n = 0 then [([], 1)] else if n = 1 then [] else [([(false, n - 1)], 1)] :=
  getD_map_range_le _ _ N n hn

end SpringerLean.RatPolyCheck
