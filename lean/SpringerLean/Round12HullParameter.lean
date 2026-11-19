import SpringerLean.Round12Caratheodory
import Mathlib.Analysis.Convex.StdSimplex

namespace SpringerLean

open Convexity
attribute [local instance] Convexity.ConvexSpace.ofModule IsModuleConvexSpace.of_module

/-- The compact three-vertex parameter space for a planar convex hull. -/
def planarHullParameters (K : Set ℂ) :
    Set ((Fin 3 → ℂ) × StdSimplex ℝ (Fin 3)) :=
  {p | ∀ i, p.1 i ∈ K}

/-- Weighted points in the three-vertex parameter space. -/
noncomputable def planarHullCombination
    (p : (Fin 3 → ℂ) × StdSimplex ℝ (Fin 3)) : ℂ :=
  ∑ i : Fin 3, (p.2.weights i) • (p.1 i)

theorem planarHullParameters_isCompact {K : Set ℂ} (hK : IsCompact K) :
    IsCompact (planarHullParameters K) := by
  have hvertices : IsCompact {p : Fin 3 → ℂ | ∀ i, p i ∈ K} :=
    isCompact_pi_infinite (fun _ => hK)
  have hprod := hvertices.prod (isCompact_univ : IsCompact (Set.univ : Set (StdSimplex ℝ (Fin 3))))
  convert hprod using 1
  ext p
  simp [planarHullParameters]

theorem planarHullCombination_continuous : Continuous planarHullCombination := by
  unfold planarHullCombination
  fun_prop

theorem planarHullImage_isCompact {K : Set ℂ} (hK : IsCompact K) :
    IsCompact (planarHullCombination '' planarHullParameters K) :=
  (planarHullParameters_isCompact hK).image planarHullCombination_continuous

theorem planarHullImage_subset_convexHull (K : Set ℂ) :
    planarHullCombination '' planarHullParameters K ⊆ convexHull ℝ K := by
  rintro x ⟨p, hp, rfl⟩
  exact mem_convexHull_of_exists_fintype
    (w := fun i : Fin 3 => p.2.weights i) (z := p.1)
    (fun i => p.2.weights_nonneg i) p.2.total_of_fintype hp rfl

theorem convexHull_subset_planarHullImage {K : Set ℂ} (hK : K.Nonempty) :
    convexHull ℝ K ⊆ planarHullCombination '' planarHullParameters K := by
  classical
  intro x hx
  obtain ⟨t, htK, htcard, hxt⟩ := complex_mem_convexHull_three_points hx
  let S : Set ℂ := t
  change x ∈ convexHull ℝ S at hxt
  rw [Set.convexHull_eq_range_iConvexComb] at hxt
  obtain ⟨v, hv⟩ := hxt
  have hcard : Fintype.card ↥S ≤ Fintype.card (Fin 3) := by
    change Fintype.card t ≤ 3
    simpa only [Fintype.card_coe] using htcard
  obtain ⟨e⟩ : Nonempty (↥S ↪ Fin 3) :=
    Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨k₀, hk₀⟩ := hK
  let p : Fin 3 → ℂ :=
    Function.extend (e : ↥S → Fin 3) (fun a => (a : ℂ)) (fun _ => k₀)
  have hp : ∀ j, p j ∈ K := by
    intro j
    by_cases hj : ∃ a : ↥S, e a = j
    · obtain ⟨a, rfl⟩ := hj
      rw [show p (e a) = (a : ℂ) from e.injective.extend_apply _ _ a]
      exact htK a.property
    · rw [show p j = k₀ from Function.extend_apply' _ _ _ hj]
      exact hk₀
  let q : (Fin 3 → ℂ) × StdSimplex ℝ (Fin 3) := (p, v.map e)
  refine ⟨q, hp, ?_⟩
  have hcomb : x = v.iConvexComb (fun a : ↥S => (a : ℂ)) := by
    simpa only [StdSimplex.affineMapMk_apply] using hv.symm
  have hmap : (v.map e).iConvexComb p =
      v.iConvexComb (fun a : ↥S => (a : ℂ)) := by
    rw [iConvexComb_map]
    congr 1
    funext a
    exact e.injective.extend_apply _ _ a
  change (∑ i : Fin 3, (v.map e).weights i • p i) = x
  calc
    _ = (v.map e).iConvexComb p := by
      rw [iConvexComb_eq_sum, Finsupp.sum_fintype _ _ (by simp)]
    _ = v.iConvexComb (fun a : ↥S => (a : ℂ)) := hmap
    _ = x := hcomb.symm

/-- The ordinary convex hull of a compact subset of the real plane is compact. -/
theorem complex_isCompact_convexHull {K : Set ℂ} (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  by_cases hne : K.Nonempty
  · have heq : convexHull ℝ K =
        planarHullCombination '' planarHullParameters K :=
      Set.Subset.antisymm (convexHull_subset_planarHullImage hne)
        (planarHullImage_subset_convexHull K)
    rw [heq]
    exact planarHullImage_isCompact hK
  · have hempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst K
    simp

/-- Lemma `br:proj`'s ordinary real convex-hull assertion for the actual
harmonic filling and the actual omitted set. -/
theorem actualHarmonic_mem_convexHull_omitted
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : ‖z‖ < 1) :
    actualHarmonic F z ∈ convexHull ℝ (exteriorOmitted F) := by
  have hclosed : IsClosed (convexHull ℝ (exteriorOmitted F)) :=
    (complex_isCompact_convexHull (exteriorOmitted_isCompact F hc)).isClosed
  have heq : closedConvexHull ℝ (exteriorOmitted F) =
      convexHull ℝ (exteriorOmitted F) := by
    rw [closedConvexHull_eq_closure_convexHull, hclosed.closure_eq]
  rw [← heq]
  exact actualHarmonic_mem_closedConvexHull_omitted F hc hz

end SpringerLean
