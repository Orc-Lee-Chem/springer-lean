import SpringerLean.Round66FiniteContraction

namespace SpringerLean

/-- The Kronecker product of two finite complex ℓ² contractions is a contraction. -/
theorem finiteComplexTensor_contraction
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (A : ι → ι → ℂ) (B : κ → κ → ℂ)
    (hA : ∀ v : ι → ℂ,
      (∑ i : ι, ‖∑ j : ι, A i j * v j‖ ^ 2) ≤ ∑ j : ι, ‖v j‖ ^ 2)
    (hB : ∀ v : κ → ℂ,
      (∑ i : κ, ‖∑ j : κ, B i j * v j‖ ^ 2) ≤ ∑ j : κ, ‖v j‖ ^ 2)
    (v : ι × κ → ℂ) :
    (∑ p : ι × κ,
      ‖∑ q : ι × κ, (A p.1 q.1 * B p.2 q.2) * v q‖ ^ 2) ≤
      ∑ q : ι × κ, ‖v q‖ ^ 2 := by
  let u : ι → κ → ℂ := fun j l => ∑ k : κ, B l k * v (j, k)
  let w : ι → κ → ℂ := fun i l => ∑ j : ι, A i j * u j l
  have hw (i : ι) (l : κ) :
      (∑ q : ι × κ, (A i q.1 * B l q.2) * v q) = w i l := by
    rw [Fintype.sum_prod_type]
    simp only [w, u, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc
    (∑ p : ι × κ,
        ‖∑ q : ι × κ, (A p.1 q.1 * B p.2 q.2) * v q‖ ^ 2) =
        ∑ l : κ, ∑ i : ι, ‖w i l‖ ^ 2 := by
          rw [Fintype.sum_prod_type]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l hl
          apply Finset.sum_congr rfl
          intro i hi
          rw [hw i l]
    _ ≤ ∑ l : κ, ∑ j : ι, ‖u j l‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro l hl
      exact hA (fun j => u j l)
    _ = ∑ j : ι, ∑ l : κ, ‖u j l‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ j : ι, ∑ k : κ, ‖v (j, k)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact hB (fun k => v (j, k))
    _ = ∑ q : ι × κ, ‖v q‖ ^ 2 := by
      rw [Fintype.sum_prod_type]

end SpringerLean