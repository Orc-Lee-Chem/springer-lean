import SpringerLean.Round2152GridWalkChain
import SpringerLean.Round2149GridCellFilling

open Set Complex
open scoped Interval

namespace SpringerLean

private theorem mem_uIcc_of_gridSignedSegment_ne_zero
    {X : ℕ → ℝ} (hX : Monotone X) {a b i : ℕ} {x : ℝ}
    (hx : x ∈ Icc (X i) (X (i+1))) (h : gridSignedSegment a b i ≠ 0) :
    x ∈ uIcc (X a) (X b) := by
  obtain ⟨hlo,hhi⟩ := gridSignedSegment_bounds h
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le (hX hab)]
    rw [min_eq_left hab] at hlo
    rw [max_eq_right hab] at hhi
    exact ⟨(hX hlo).trans hx.1,hx.2.trans (hX hhi)⟩
  · rw [uIcc_of_ge (hX hba)]
    rw [min_eq_right hba] at hlo
    rw [max_eq_left hba] at hhi
    exact ⟨(hX hlo).trans hx.1,hx.2.trans (hX hhi)⟩

def GridPointAtInteriorIndex (X Y : ℕ → ℝ) (N : ℕ) (z : ℂ) : Prop :=
  let i := readGridIndex X z.re
  let j := readGridIndex Y z.im
  0 < i ∧ i < N ∧ 0 < j ∧ j < N ∧ X i = z.re ∧ Y j = z.im

theorem gridPointAtInteriorIndex_of_coordinates
    {X Y : ℕ → ℝ} {N : ℕ} (hX : StrictMono X) (hY : StrictMono Y) {z : ℂ}
    (h : ∃ i j, 0 < i ∧ i < N ∧ 0 < j ∧ j < N ∧ z.re = X i ∧ z.im = Y j) :
    GridPointAtInteriorIndex X Y N z := by
  obtain ⟨i,j,hi,hI,hj,hJ,he,he'⟩ := h
  unfold GridPointAtInteriorIndex
  rw [readGridIndex_eq X hX he.symm,readGridIndex_eq Y hY he'.symm]
  exact ⟨hi,hI,hj,hJ,he.symm,he'.symm⟩

private theorem gridStep_horizontal_trace
    {X Y : ℕ → ℝ} (hX : StrictMono X) {z w : ℂ} {a b c d i j : ℕ}
    (hx : X a = z.re) (hy : Y b = z.im) (hx' : X c = w.re)
    (h : (gridStepCoefficients a b c d).1 i j ≠ 0) :
    gridHorizontalEdge X Y i j ⊆ Rectangle z w := by
  intro u hu
  have hb : b = j := by
    by_contra he
    exact h (by simp [gridStepCoefficients,gridIndexMass,he])
  have hs : gridSignedSegment a c i ≠ 0 := by
    intro he
    exact h (by simp [gridStepCoefficients,he])
  have hre := mem_uIcc_of_gridSignedSegment_ne_zero hX.monotone hu.1 hs
  rw [hx,hx'] at hre
  have him : u.im = z.im := (show u.im = Y j from hu.2).trans (hb ▸ hy)
  exact ⟨hre,him.symm ▸ left_mem_uIcc⟩

private theorem gridStep_vertical_trace
    {X Y : ℕ → ℝ} (hY : StrictMono Y) {z w : ℂ} {a b c d i j : ℕ}
    (hy : Y b = z.im) (hx' : X c = w.re) (hy' : Y d = w.im)
    (h : (gridStepCoefficients a b c d).2 i j ≠ 0) :
    gridVerticalEdge X Y i j ⊆ Rectangle z w := by
  intro u hu
  have hc : c = i := by
    by_contra he
    exact h (by simp [gridStepCoefficients,gridIndexMass,he])
  have hs : gridSignedSegment b d j ≠ 0 := by
    intro he
    exact h (by simp [gridStepCoefficients,he])
  have him := mem_uIcc_of_gridSignedSegment_ne_zero hY.monotone hu.2 hs
  rw [hy,hy'] at him
  have hre : u.re = w.re := (show u.re = X i from hu.1).trans (hc ▸ hx')
  exact ⟨hre.symm ▸ right_mem_uIcc,him⟩

namespace RectilinearWalk

variable {U : Set ℂ} {a b : ℂ}

theorem gridCoefficients_support
    {X Y : ℕ → ℝ} {N : ℕ} (hX : StrictMono X) (hY : StrictMono Y)
    (p : RectilinearWalk U a b)
    (hcoords : ∀ z ∈ p.vertices, GridPointAtInteriorIndex X Y N z) :
    let H := (p.gridCoefficients X Y).1
    let V := (p.gridCoefficients X Y).2
    (∀ i, H i 0 = 0) ∧ (∀ j, H 0 j = 0) ∧ (∀ j, V 0 j = 0) ∧
    (∀ i j, N ≤ j → V i j = 0) ∧ (∀ i j, N ≤ i → H i j = 0) ∧
    (∀ i j, H i j ≠ 0 → gridHorizontalEdge X Y i j ⊆ p.trace) ∧
    (∀ i j, V i j ≠ 0 → gridVerticalEdge X Y i j ⊆ p.trace) := by
  classical
  induction p with
  | point => simp [gridCoefficients]
  | @step z w p ax hz ih =>
    have hp (v : ℂ) (hv : v ∈ p.vertices) : GridPointAtInteriorIndex X Y N v :=
      hcoords v (Finset.mem_insert_of_mem hv)
    obtain ⟨hbottom,hleft,hVleft,htop,hright,hH,hV⟩ := ih hp
    obtain ⟨hxlo,hxhi,hylo,hyhi,hx,hy⟩ := hp z p.target_mem_vertices
    obtain ⟨hxlo',hxhi',hylo',hyhi',hx',hy'⟩ := hcoords w (Finset.mem_insert_self _ _)
    let c := readGridIndex X z.re
    let d := readGridIndex Y z.im
    let c' := readGridIndex X w.re
    let d' := readGridIndex Y w.im
    let A := p.gridCoefficients X Y
    let B := gridStepCoefficients c d c' d'
    change (∀ i, (A+B).1 i 0 = 0) ∧ (∀ j, (A+B).1 0 j = 0) ∧ (∀ j, (A+B).2 0 j = 0) ∧
      (∀ i j, N ≤ j → (A+B).2 i j = 0) ∧ (∀ i j, N ≤ i → (A+B).1 i j = 0) ∧
      (∀ i j, (A+B).1 i j ≠ 0 → gridHorizontalEdge X Y i j ⊆ p.trace ∪ Rectangle z w) ∧
      (∀ i j, (A+B).2 i j ≠ 0 → gridVerticalEdge X Y i j ⊆ p.trace ∪ Rectangle z w)
    simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply]
    refine ⟨fun i => ?_,fun j => ?_,fun j => ?_,fun i j hj => ?_,fun i j hi => ?_,
      fun i j hn => ?_,fun i j hn => ?_⟩
    · have hn : d ≠ 0 := Nat.ne_of_gt hylo
      simp [A,B,gridStepCoefficients,gridIndexMass,hn,hbottom]
    · have hs : gridSignedSegment c c' 0 = 0 := gridSignedSegment_eq_zero_left hxlo hxlo'
      simp [A,B,gridStepCoefficients,hs,hleft]
    · have hn : c' ≠ 0 := Nat.ne_of_gt hxlo'
      simp [A,B,gridStepCoefficients,gridIndexMass,hn,hVleft]
    · have hs : gridSignedSegment d d' j = 0 :=
        gridSignedSegment_eq_zero_right (hyhi.le.trans hj) (hyhi'.le.trans hj)
      simp [A,B,gridStepCoefficients,hs,htop i j hj]
    · have hs : gridSignedSegment c c' i = 0 :=
        gridSignedSegment_eq_zero_right (hxhi.le.trans hi) (hxhi'.le.trans hi)
      simp [A,B,gridStepCoefficients,hs,hright i j hi]
    · by_cases h : A.1 i j = 0
      · have h' : B.1 i j ≠ 0 := by simpa only [h,zero_add] using hn
        exact (gridStep_horizontal_trace hX hx hy hx' h').trans subset_union_right
      · exact (hH i j h).trans subset_union_left
    · by_cases h : A.2 i j = 0
      · have h' : B.2 i j ≠ 0 := by simpa only [h,zero_add] using hn
        exact (gridStep_vertical_trace hY hy hx' hy' h').trans subset_union_right
      · exact (hV i j h).trans subset_union_left

end RectilinearWalk

end SpringerLean
