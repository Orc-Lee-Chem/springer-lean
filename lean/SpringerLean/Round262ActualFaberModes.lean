import SpringerLean.Round261CommonFaberCombination
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Rev

namespace SpringerLean
open PowerSeries

theorem exteriorFaberCombination_head_coeff
    (N : ℕ) (α : Fin N → ℂ) (k : Fin N) :
    PowerSeries.coeff k.val
      (∑ i : Fin N, PowerSeries.C (α i) * PowerSeries.X ^ (N - (i.val + 1))) =
      α k.rev := by
  classical
  rw [map_sum, Finset.sum_eq_single k.rev]
  · have hid : N - (k.rev.val + 1) = k.val := by
      simp only [Fin.val_rev]
      omega
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, hid,
      ite_true, mul_one]
  · intro i hi hne
    have hid : k.val ≠ N - (i.val + 1) := by
      intro heq
      apply hne
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, hid]
  · simp

theorem exteriorFaberCombination_actual_lowCoeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (N : ℕ) (α : Fin N → ℂ) (k : Fin N) :
    actualTaylorCoeff (exteriorFaberCombinationFactor F N α) k.val = α k.rev := by
  rw [← actualTaylorSeries_coeff,
    exteriorFaberCombination_actualTaylorSeries F hc N α, map_add,
    exteriorFaberCombination_head_coeff]
  simp [PowerSeries.coeff_X_pow_mul', Nat.not_le.mpr k.isLt]

theorem exteriorFaberCombination_actual_negativeCoeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (N : ℕ) (α : Fin N → ℂ) (j : ℕ) :
    actualTaylorCoeff (exteriorFaberCombinationFactor F N α) (N + (j + 1)) =
      ∑ i : Fin N, α i * ((i.val + 1 : ℕ) : ℂ) *
        PowerSeries.coeff (j + 1)
          (PowerSeries.coeff (i.val + 1) (exteriorFormalGrunskyKernel F)) := by
  rw [← actualTaylorSeries_coeff,
    exteriorFaberCombination_actualTaylorSeries F hc N α, map_add]
  have hhead : PowerSeries.coeff (N + (j + 1))
      (∑ i : Fin N, PowerSeries.C (α i) *
        PowerSeries.X ^ (N - (i.val + 1))) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    have hne : N + (j + 1) ≠ N - (i.val + 1) := by omega
    simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, hne]
  rw [hhead, zero_add]
  simp only [PowerSeries.coeff_X_pow_mul', Nat.le_add_right,
    ite_true, Nat.add_sub_cancel_left, map_sum, PowerSeries.coeff_C_mul]

theorem exteriorFaberCombination_actual_positive_energy
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (N : ℕ) (α : Fin N → ℂ) :
    (∑ k ∈ Finset.range N,
      ((N : ℝ) - k) * ‖actualTaylorCoeff (exteriorFaberCombinationFactor F N α) k‖ ^ 2) =
      ∑ i : Fin N, ((i.val + 1 : ℕ) : ℝ) * ‖α i‖ ^ 2 := by
  rw [Finset.sum_range]
  simp_rw [exteriorFaberCombination_actual_lowCoeff F hc N α]
  calc
    _ = ∑ k : Fin N, ((k.rev.val + 1 : ℕ) : ℝ) * ‖α k.rev‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hn : N = k.val + (k.rev.val + 1) := by
        simp only [Fin.val_rev]
        omega
      have hr : (N : ℝ) = (k.val : ℝ) + ((k.rev.val + 1 : ℕ) : ℝ) := by
        exact_mod_cast hn
      rw [hr]
      ring
    _ = _ := Equiv.sum_comp Fin.revPerm
      (fun i : Fin N => ((i.val + 1 : ℕ) : ℝ) * ‖α i‖ ^ 2)

end SpringerLean
