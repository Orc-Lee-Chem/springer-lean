import SpringerLean.Round770ChebyshevRolleChain

namespace SpringerLean

open Polynomial

/-- The ordered Rolle grid exhausts all real roots of the `j`th Chebyshev
derivative, with every root occurring once. -/
theorem chebyshevRolleChain_roots (n j : ℕ) (hj : j < n) :
    ((derivative^[j]) (Chebyshev.T ℝ (n : ℤ))).roots =
      ((Finset.range (n - j)).image
        (fun k => (chebyshevRolleChain n j hj.le).grid j k)).val := by
  let C := chebyshevRolleChain n j hj.le
  let P := (derivative^[j]) (Chebyshev.T ℝ (n : ℤ))
  have hanti : StrictAntiOn (C.grid j) (Set.Iio (n - j)) := by
    apply strictAntiOn_of_succ_lt Set.ordConnected_Iio
    intro k _ hk hk1
    exact C.descending j (by omega) k (by simp at hk1; omega)
  have hinj : Set.InjOn (C.grid j) (Finset.range (n - j)) := by
    apply hanti.injOn.mono
    intro k hk
    simpa using hk
  have hcard : ((Finset.range (n - j)).image (C.grid j)).card = n - j := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hdegree : P.natDegree = n - j := by
    have hlower := P.card_roots'
    have hupper := natDegree_iterate_derivative (Chebyshev.T ℝ (n : ℤ)) j
    rw [Chebyshev.natDegree_T, Int.natAbs_natCast] at hupper
    change P.natDegree ≤ n - j at hupper
    change P.roots.card ≤ P.natDegree at hlower
    rw [chebyshev_iterated_derivative_real_roots] at hlower
    omega
  have hnonzero : P ≠ 0 := by
    intro hp
    have hc := chebyshev_iterated_derivative_real_roots n j
    change P.roots.card = n - j at hc
    rw [hp] at hc
    simp at hc
    omega
  have hroots : ∀ z ∈ (Finset.range (n - j)).image (C.grid j), P.eval z = 0 := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact C.roots j (by omega) k (Finset.mem_range.mp hk)
  change P.roots = _
  exact roots_eq_of_natDegree_le_card_of_ne_zero hroots
    (by rw [hdegree, hcard]) hnonzero

theorem upperGridCount_eq_image_filter_card
    (m : ℕ) (x : ℕ → ℝ) (t : ℝ)
    (hinj : Set.InjOn x (Finset.range m)) :
    (((Finset.range m).image x).val.filter (fun z => t ≤ z)).card =
      upperGridCount x m t := by
  classical
  change (((Finset.range m).image x).filter (fun z => t ≤ z)).card = _
  rw [Finset.filter_image]
  have hsub : Set.InjOn x ((Finset.range m).filter (fun k => t ≤ x k)) :=
    hinj.mono (by exact Finset.filter_subset _ _)
  rw [Finset.card_image_of_injOn hsub]
  exact (Finset.card_filter (fun k => t ≤ x k) (Finset.range m)).trans rfl

end SpringerLean

#print axioms SpringerLean.chebyshevRolleChain_roots
#print axioms SpringerLean.upperGridCount_eq_image_filter_card
