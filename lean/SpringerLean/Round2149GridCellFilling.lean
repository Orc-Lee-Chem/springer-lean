import SpringerLean.Round2145CompactFillingInsideDomain
import SpringerLean.Round2144GridCycleWeights
import Mathlib.Analysis.Complex.ReImTopology

open Set Complex

namespace SpringerLean

private theorem compact_subset_filling_of_frontier_subset
    {P B : Set ℂ} (hB : IsCompact B) (hfront : frontier B ⊆ P) :
    B ⊆ continuumFill P := by
  intro z hz
  by_cases hzP : z ∈ P
  · exact Or.inl hzP
  let D := connectedComponentIn Pᶜ z
  have hD : z ∈ D := mem_connectedComponentIn hzP
  have hcover : D ⊆ interior B ∪ Bᶜ := by
    intro w hw
    by_cases h : w ∈ B
    · left
      by_contra hn
      exact connectedComponentIn_subset Pᶜ z hw (hfront ⟨subset_closure h,hn⟩)
    · exact Or.inr h
  have hzI : z ∈ interior B := (hcover hD).resolve_right (not_not_intro hz)
  have hd : Disjoint (interior B) Bᶜ :=
    Set.disjoint_left.mpr (fun _ h₁ h₂ => h₂ (interior_subset h₁))
  have hsub := isPreconnected_connectedComponentIn.subset_left_of_subset_union
    isOpen_interior hB.isClosed.isOpen_compl hd hcover ⟨z,hD,hzI⟩
  exact Or.inr (hB.isBounded.subset (hsub.trans interior_subset))

def gridCell (X Y : ℕ → ℝ) (i j : ℕ) : Set ℂ :=
  Icc (X i) (X (i+1)) ×ℂ Icc (Y j) (Y (j+1))

def gridHorizontalEdge (X Y : ℕ → ℝ) (i j : ℕ) : Set ℂ :=
  Icc (X i) (X (i+1)) ×ℂ {Y j}

def gridVerticalEdge (X Y : ℕ → ℝ) (i j : ℕ) : Set ℂ :=
  {X i} ×ℂ Icc (Y j) (Y (j+1))

private theorem mem_some_interval
    (X : ℕ → ℝ) (N : ℕ) {x : ℝ} (hx : x ∈ Icc (X 0) (X (N+1))) :
    ∃ i : Fin (N+1), x ∈ Icc (X i) (X (i.val+1)) := by
  induction N with
  | zero => exact ⟨0,hx⟩
  | succ N ih =>
    by_cases h : x ≤ X (N+1)
    · obtain ⟨i,hi⟩ := ih ⟨hx.1,h⟩
      exact ⟨i.castSucc,hi⟩
    · exact ⟨Fin.last (N+1),le_of_lt (lt_of_not_ge h),hx.2⟩

private theorem adjacent_interval_indices
    {X : ℕ → ℝ} (hX : StrictMono X) {x : ℝ} {i j : ℕ}
    (hi : x ∈ Icc (X i) (X (i+1))) (hj : x ∈ Icc (X j) (X (j+1))) :
    i=j ∨ i+1=j ∨ j+1=i := by
  have h₁ := hX.le_iff_le.mp (hi.1.trans hj.2)
  have h₂ := hX.le_iff_le.mp (hj.1.trans hi.2)
  omega

/-- If the nonzero edges of a compactly supported grid cycle lie on
the trace, every cell carrying a nonzero weight is in its filling. -/
theorem gridCell_subset_filling_of_weight_ne_zero
    {A : Type*} [AddCommGroup A]
    (X Y : ℕ → ℝ) (hX : StrictMono X) (hY : StrictMono Y)
    (H V : ℕ → ℕ → A) (N : ℕ) (P : Set ℂ)
    (hbase : ∀ i, H i 0 = H (i+1) 0 + V (i+1) 0)
    (hbalance : ∀ i j, H i (j+1) + V (i+1) j = H (i+1) (j+1) + V (i+1) (j+1))
    (hbottom : ∀ i, H i 0 = 0) (hleft : ∀ j, H 0 j = 0)
    (htop : ∀ i j, N ≤ j → V i j = 0)
    (hright : ∀ i j, N ≤ i → H i j = 0)
    (hH : ∀ i j, H i j ≠ 0 → gridHorizontalEdge X Y i j ⊆ P)
    (hV : ∀ i j, V i j ≠ 0 → gridVerticalEdge X Y i j ⊆ P)
    {i j : ℕ} (hw : gridCellWeight H i j ≠ 0) :
    gridCell X Y i j ⊆ continuumFill P := by
  classical
  let W := gridCellWeight H
  let B := ⋃ i : Fin (N+1), ⋃ j : Fin (N+1),
    if W i j ≠ 0 then gridCell X Y i j else ∅
  let B₀ := ⋃ i : Fin (N+1), ⋃ j : Fin (N+1),
    if W i j = 0 then gridCell X Y i j else ∅
  have hC (i j : ℕ) : IsCompact (gridCell X Y i j) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hB : IsCompact B := by
    apply isCompact_iUnion
    intro i
    apply isCompact_iUnion
    intro j
    split_ifs
    · exact hC _ _
    · exact isCompact_empty
  have hB₀ : IsClosed B₀ := by
    apply isClosed_iUnion_of_finite
    intro i
    apply isClosed_iUnion_of_finite
    intro j
    split_ifs
    · exact (hC _ _).isClosed
    · exact isClosed_empty
  have hsupport := gridCellWeight_support H V N hbase hbalance hleft htop hright
  have hinner (i j : ℕ) (hn : W i j ≠ 0) :
      0 < i ∧ 0 < j ∧ i < N ∧ j < N := by
    refine ⟨?_,?_,lt_of_not_ge (fun h => hn (hsupport i j (Or.inl h))),
      lt_of_not_ge (fun h => hn (hsupport i j (Or.inr h)))⟩
    · by_contra! hi
      obtain rfl : i = 0 := by omega
      exact hn (gridCellWeight_eq_zero_of_column_eq_zero H 0 j hleft)
    · by_contra! hj
      obtain rfl : j = 0 := by omega
      exact hn ((gridCellWeight_base H i).trans (hbottom i))
  have hmatch (z : ℂ) (hz : z ∉ P) (i s j t : ℕ)
      (h₁ : z ∈ gridCell X Y i j) (h₂ : z ∈ gridCell X Y s t) : W i j = W s t := by
    have hstepX (i j : ℕ) (ha : z ∈ gridCell X Y i j) (hb : z ∈ gridCell X Y (i+1) j) :
        W i j = W (i+1) j := by
      have hV₀ : V (i+1) j = 0 := by
        by_contra hn
        apply hz
        exact hV _ _ hn ⟨le_antisymm ha.1.2 hb.1.1,ha.2⟩
      exact sub_eq_zero.mp ((gridCellWeight_vertical H V hbase hbalance i j).trans hV₀)
    have hstepY (i j : ℕ) (ha : z ∈ gridCell X Y i j) (hb : z ∈ gridCell X Y i (j+1)) :
        W i j = W i (j+1) := by
      have hH₀ : H i (j+1) = 0 := by
        by_contra hn
        apply hz
        exact hH _ _ hn ⟨ha.1,le_antisymm ha.2.2 hb.2.1⟩
      exact (sub_eq_zero.mp ((gridCellWeight_horizontal H i j).trans hH₀)).symm
    have h₃ : z ∈ gridCell X Y s j := ⟨h₂.1,h₁.2⟩
    have hx : W i j = W s j := by
      rcases adjacent_interval_indices hX (i := i) (j := s) h₁.1 h₃.1 with he | he | he
      · subst s; rfl
      · subst s; exact hstepX _ _ h₁ h₃
      · subst i; exact (hstepX _ _ h₃ h₁).symm
    have hy : W s j = W s t := by
      rcases adjacent_interval_indices hY (i := j) (j := t) h₃.2 h₂.2 with he | he | he
      · subst t; rfl
      · subst t; exact hstepY _ _ h₃ h₂
      · subst j; exact (hstepY _ _ h₂ h₃).symm
    exact hx.trans hy
  have hf : frontier B ⊆ P := by
    intro z hz
    by_contra hzP
    have hzB : z ∈ B := by simpa only [hB.isClosed.closure_eq] using hz.1
    obtain ⟨i,j,hij⟩ := mem_iUnion.mp hzB |>.imp fun i hi => mem_iUnion.mp hi
    have hwi : W i j ≠ 0 := by
      by_contra h
      simp [h] at hij
    have hzi : z ∈ gridCell X Y i j := by simpa only [if_pos hwi] using hij
    have hnB₀ : z ∉ B₀ := by
      intro h
      obtain ⟨s,t,hst⟩ := mem_iUnion.mp h |>.imp fun s hs => mem_iUnion.mp hs
      have hwt : W s t = 0 := by by_contra hn; simp [hn] at hst
      have hzt : z ∈ gridCell X Y s t := by simpa only [if_pos hwt] using hst
      exact hwi ((hmatch z hzP _ _ _ _ hzi hzt).trans hwt)
    let O := Ioo (X 0) (X (N+1)) ×ℂ Ioo (Y 0) (Y (N+1))
    have hO : IsOpen O := isOpen_Ioo.reProdIm isOpen_Ioo
    have hzO : z ∈ O := by
      obtain ⟨hi,hj,hI,hJ⟩ := hinner i j hwi
      exact ⟨⟨(hX hi).trans_le hzi.1.1,hzi.1.2.trans_lt (hX (by omega))⟩,
        ⟨(hY hj).trans_le hzi.2.1,hzi.2.2.trans_lt (hY (by omega))⟩⟩
    have hcover : O \ B₀ ⊆ B := by
      rintro v ⟨hvo,hv₀⟩
      obtain ⟨i,hi⟩ := mem_some_interval X N ⟨hvo.1.1.le,hvo.1.2.le⟩
      obtain ⟨j,hj⟩ := mem_some_interval Y N ⟨hvo.2.1.le,hvo.2.2.le⟩
      have hwi : W i j ≠ 0 := by
        intro h
        exact hv₀ (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,by simpa only [if_pos h] using
          (show v ∈ gridCell X Y i j from ⟨hi,hj⟩)⟩⟩)
      exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,by simpa only [if_pos hwi] using
        (show v ∈ gridCell X Y i j from ⟨hi,hj⟩)⟩⟩
    exact hz.2 (interior_maximal hcover (hO.sdiff hB₀) ⟨hzO,hnB₀⟩)
  apply Subset.trans _ (compact_subset_filling_of_frontier_subset hB hf)
  intro z hz
  obtain ⟨_,_,hi,hj⟩ := hinner i j hw
  let fi : Fin (N+1) := ⟨i,by omega⟩
  let fj : Fin (N+1) := ⟨j,by omega⟩
  have hwi : W fi fj ≠ 0 := hw
  exact mem_iUnion.mpr ⟨fi,mem_iUnion.mpr ⟨fj,by simpa only [if_pos hwi] using hz⟩⟩

end SpringerLean
