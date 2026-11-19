import SpringerLean.Round1939FactorConstantDefinitions
import SpringerLean.Round2065PolynomialRootBiholomorphism
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.Connected.LocallyConnected

open Set Polynomial Metric Topology Bornology

namespace SpringerLean

/-- The boundary of a complementary component of a closed plane set
lies in that closed set. -/
theorem frontier_complementary_component_subset
    (K : Set ℂ) (hK : IsClosed K) (x : ℂ) :
    frontier (connectedComponentIn Kᶜ x) ⊆ K := by
  by_cases hx : x ∈ Kᶜ
  · let e : ↥(Kᶜ) := ⟨x,hx⟩
    let U := connectedComponentIn Kᶜ x
    have hU : IsOpen U := hK.isOpen_compl.connectedComponentIn
    have hUeq : U = Subtype.val '' connectedComponent e := connectedComponentIn_eq_image hx
    intro z hz
    by_contra hzK
    have hz' : (⟨z,hzK⟩ : ↥(Kᶜ)) ∈ closure (connectedComponent e) := by
      rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, ← hUeq]
      exact frontier_subset_closure hz
    rw [isClosed_connectedComponent.closure_eq] at hz'
    have hm : z ∈ U := by rw [hUeq]; exact mem_image_of_mem Subtype.val hz'
    exact hz.2 (by rwa [hU.interior_eq])
  · simp [connectedComponentIn_eq_empty hx]

/-- Filling a bounded complementary component preserves the bound
on each actual polynomial evaluation. -/
theorem polynomial_eval_norm_le_of_bounded_component
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty) (P : ℂ[X])
    (x : ℂ) (hx : x ∉ K) (hbound : IsBounded (connectedComponentIn Kᶜ x)) :
    ‖P.eval x‖ ≤ continuumPolynomialNorm K P := by
  obtain ⟨z,hz,hmax⟩ := continuumPolynomialNorm_attained K hK hne P
  rw [continuumPolynomialNorm_eq_at_max K hK hne P hz hmax]
  apply Complex.norm_le_of_forall_mem_frontier_norm_le hbound
    P.differentiable.diffContOnCl
  · exact fun y hy => hmax y (frontier_complementary_component_subset K hK.isClosed x hy)
  · exact subset_closure (mem_connectedComponentIn hx)

/-- The filling of a compact plane set is formed by adjoining all its
bounded complementary components. -/
def continuumFill (K : Set ℂ) : Set ℂ :=
  K ∪ {z | IsBounded (connectedComponentIn Kᶜ z)}

theorem subset_continuumFill (K : Set ℂ) : K ⊆ continuumFill K := subset_union_left

theorem isClosed_continuumFill (K : Set ℂ) (hK : IsClosed K) :
    IsClosed (continuumFill K) := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hzK : z ∉ K := fun h => hz (Or.inl h)
  have hzu : ¬ IsBounded (connectedComponentIn Kᶜ z) := fun h => hz (Or.inr h)
  apply Filter.mem_of_superset (hK.isOpen_compl.connectedComponentIn.mem_nhds
    (mem_connectedComponentIn hzK))
  intro w hw
  have hwK : w ∉ K := connectedComponentIn_subset Kᶜ z hw
  have huw := connectedComponentIn_eq hw
  exact fun hw' => hw'.elim hwK (fun h => hzu (huw ▸ h))

theorem isBounded_continuumFill (K : Set ℂ) (hK : IsCompact K) :
    IsBounded (continuumFill K) := by
  obtain ⟨R,hRK⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  let r := max R 1
  have hr : 0 < r := zero_lt_one.trans_le (le_max_right _ _)
  have hRK' : K ⊆ closedBall (0:ℂ) r := hRK.trans (closedBall_subset_closedBall (le_max_left _ _))
  let O : Set ℂ := {z | r < ‖z‖}
  have hO : IsConnected O := complex_norm_gt_isConnected r hr.le
  have hOb : ¬ IsBounded O := by
    intro hb
    obtain ⟨C,hC⟩ := hb.exists_norm_le
    let w := max r C + 1
    have hw0 : 0 ≤ w := by dsimp [w]; linarith [le_max_left r C]
    have hwO : (w : ℂ) ∈ O := by
      change r < ‖(w:ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
      dsimp [w]
      linarith [le_max_left r C]
    have hle := hC (w : ℂ) hwO
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0] at hle
    dsimp [w] at hle
    linarith [le_max_right r C]
  have hsub : O ⊆ Kᶜ := by
    intro z hz hk
    have hh := mem_closedBall_zero_iff.mp (hRK' hk)
    exact (not_lt_of_ge hh) hz
  apply isBounded_closedBall.subset
  intro z hz
  by_contra hzn
  have hzO : z ∈ O := lt_of_not_ge (fun h => hzn (mem_closedBall_zero_iff.mpr h))
  exact hz.elim (fun h => hsub hzO h) (fun h => hOb
    ((show IsBounded (connectedComponentIn Kᶜ z) from h).subset
      (hO.isPreconnected.subset_connectedComponentIn hzO hsub)))

theorem isCompact_continuumFill (K : Set ℂ) (hK : IsCompact K) :
    IsCompact (continuumFill K) :=
  isCompact_of_isClosed_isBounded (isClosed_continuumFill K hK.isClosed) (isBounded_continuumFill K hK)

theorem continuumPolynomialNorm_fill_eq (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (P : ℂ[X]) : continuumPolynomialNorm (continuumFill K) P = continuumPolynomialNorm K P := by
  obtain ⟨z,hz,hmax⟩ := continuumPolynomialNorm_attained K hK hne P
  have hnorm := continuumPolynomialNorm_eq_at_max K hK hne P hz hmax
  apply (continuumPolynomialNorm_eq_at_max (continuumFill K) (isCompact_continuumFill K hK)
    (hne.mono (subset_continuumFill K)) P (subset_continuumFill K hz) ?_).trans hnorm.symm
  intro w hw
  by_cases hwK : w ∈ K
  · exact hmax w hwK
  · rw [← hnorm]
    exact polynomial_eval_norm_le_of_bounded_component K hK hne P w hwK
      (hw.resolve_left hwK)

theorem factorConstant_fill_eq (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty) :
    factorConstant (continuumFill K) = factorConstant K := by
  have h (c : ℝ) : FactorInequality (continuumFill K) c ↔ FactorInequality K c := by
    unfold FactorInequality
    simp only [continuumPolynomialNorm_fill_eq K hK hne]
  unfold factorConstant
  congr 1
  ext c
  exact and_congr_right (fun _ => h c)

end SpringerLean
