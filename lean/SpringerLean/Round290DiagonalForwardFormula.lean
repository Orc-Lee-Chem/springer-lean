import SpringerLean.Round288SchoberPrincipal

namespace SpringerLean
open PowerSeries

theorem schoberActualA_forward_formula
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (n j : ℕ) (hj : j ≤ n) :
    schoberActualA F (n + 1) (j + 1) =
      (((j + 1 : ℕ) : ℂ) / ((n + 1 : ℕ) : ℂ)) *
        PowerSeries.coeff (n - j)
          (formalExteriorPhi (exteriorFormalForward F) ^ (n + 1)) := by
  have h := schoberActualA_lagrange F hc n j hj
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  apply (mul_left_cancel₀ hn)
  calc
    ((n + 1 : ℕ) : ℂ) * schoberActualA F (n + 1) (j + 1) = _ := h
    _ = _ := by field_simp

theorem schoberActualDiagonal_forward_formula
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (n : ℕ) :
    schoberActualDiagonal F (n + 1) =
      ∑ j ∈ Finset.range (n + 1),
        ((((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ 2) *
          ‖PowerSeries.coeff (n - j)
            (formalExteriorPhi (exteriorFormalForward F) ^ (n + 1))‖ ^ 2 := by
  classical
  have hsum : (∑ j ∈ Finset.Icc 1 (n + 1), ‖schoberActualA F (n + 1) j‖ ^ 2) =
      ∑ j ∈ Finset.range (n + 1), ‖schoberActualA F (n + 1) (j + 1)‖ ^ 2 := by
    apply Finset.sum_bij (fun j hj => j - 1)
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      simp only [Finset.mem_range]
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_Icc] at ha hb
      omega
    · intro j hj
      refine ⟨j + 1, ?_, by omega⟩
      simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
      omega
    · intro j hj
      have hj1 := (Finset.mem_Icc.mp hj).1
      simp only [Nat.sub_add_cancel hj1]
  rw [schoberActualDiagonal, hsum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [schoberActualA_forward_formula F hc n j (by have := Finset.mem_range.mp hj; omega),
    norm_mul, mul_pow]
  simp only [norm_div, Complex.norm_natCast, div_pow]

end SpringerLean
