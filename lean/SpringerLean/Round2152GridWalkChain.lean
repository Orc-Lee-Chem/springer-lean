import SpringerLean.Round2151RectilinearGridCoordinates

open Set

namespace SpringerLean

noncomputable def readGridIndex (X : ℕ → ℝ) (x : ℝ) : ℕ := by
  classical
  exact if h : ∃ i, X i = x then Classical.choose h else 0

theorem readGridIndex_eq (X : ℕ → ℝ) (hX : StrictMono X) {x : ℝ} {i : ℕ}
    (hi : X i = x) : readGridIndex X x = i := by
  have h : ∃ i, X i = x := ⟨i,hi⟩
  rw [readGridIndex,dif_pos h]
  exact hX.injective ((Classical.choose_spec h).trans hi.symm)

def gridIndexMass (a i : ℕ) : ℂ := if a = i then 1 else 0

def gridIndexStep (a i : ℕ) : ℂ := if a ≤ i then 1 else 0

def gridSignedSegment (a b i : ℕ) : ℂ := gridIndexStep a i - gridIndexStep b i

private def gridPrevious (L : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | i+1 => L i

private theorem gridIndexStep_difference (a i : ℕ) :
    gridIndexStep a i - gridPrevious (gridIndexStep a) i = gridIndexMass a i := by
  cases i with
  | zero => simp [gridIndexStep,gridPrevious,gridIndexMass]
  | succ i =>
    simp only [gridIndexStep,gridPrevious,gridIndexMass]
    split_ifs <;> (first | omega | norm_num)

private theorem gridSignedSegment_difference (a b i : ℕ) :
    gridSignedSegment a b i - gridPrevious (gridSignedSegment a b) i =
      gridIndexMass a i - gridIndexMass b i := by
  rw [←gridIndexStep_difference a,←gridIndexStep_difference b]
  cases i <;> simp only [gridPrevious,gridSignedSegment] <;> ring

theorem gridSignedSegment_eq_zero_left {a b i : ℕ} (ha : i < a) (hb : i < b) :
    gridSignedSegment a b i = 0 := by
  simp only [gridSignedSegment,gridIndexStep,if_neg (not_le_of_gt ha),if_neg (not_le_of_gt hb),sub_self]

theorem gridSignedSegment_eq_zero_right {a b i : ℕ} (ha : a ≤ i) (hb : b ≤ i) :
    gridSignedSegment a b i = 0 := by
  simp only [gridSignedSegment,gridIndexStep,if_pos ha,if_pos hb,sub_self]

theorem gridSignedSegment_bounds {a b i : ℕ} (h : gridSignedSegment a b i ≠ 0) :
    min a b ≤ i ∧ i+1 ≤ max a b := by
  constructor
  · by_contra! hl
    exact h (gridSignedSegment_eq_zero_left (hl.trans_le (min_le_left _ _))
      (hl.trans_le (min_le_right _ _)))
  · by_contra! hr
    have hh : max a b ≤ i := by omega
    exact h (gridSignedSegment_eq_zero_right ((le_max_left a b).trans hh)
      ((le_max_right a b).trans hh))

abbrev GridEdgeCoefficients := (ℕ → ℕ → ℂ) × (ℕ → ℕ → ℂ)

def gridStepCoefficients (a b c d : ℕ) : GridEdgeCoefficients :=
  (fun i j => gridIndexMass b j * gridSignedSegment a c i,
   fun i j => gridIndexMass c i * gridSignedSegment b d j)

def gridDivergence (W : GridEdgeCoefficients) (i j : ℕ) : ℂ :=
  W.1 i j - gridPrevious (fun k => W.1 k j) i +
    (W.2 i j - gridPrevious (W.2 i) j)

theorem gridDivergence_add (W V : GridEdgeCoefficients) (i j : ℕ) :
    gridDivergence (W+V) i j = gridDivergence W i j + gridDivergence V i j := by
  cases i <;> cases j <;> simp only [gridDivergence,gridPrevious,Prod.fst_add,Prod.snd_add,Pi.add_apply] <;> ring

theorem gridDivergence_zero (i j : ℕ) : gridDivergence 0 i j = 0 := by
  cases i <;> cases j <;> simp [gridDivergence,gridPrevious]

theorem gridDivergence_step (a b c d i j : ℕ) :
    gridDivergence (gridStepCoefficients a b c d) i j =
      gridIndexMass a i * gridIndexMass b j - gridIndexMass c i * gridIndexMass d j := by
  have hH : gridPrevious (fun k => gridIndexMass b j * gridSignedSegment a c k) i =
      gridIndexMass b j * gridPrevious (gridSignedSegment a c) i := by
    cases i <;> simp [gridPrevious]
  have hV : gridPrevious (fun k => gridIndexMass c i * gridSignedSegment b d k) j =
      gridIndexMass c i * gridPrevious (gridSignedSegment b d) j := by
    cases j <;> simp [gridPrevious]
  simp only [gridDivergence,gridStepCoefficients,hH,hV,←mul_sub,gridSignedSegment_difference]
  ring

namespace RectilinearWalk

variable {U : Set ℂ} {a b : ℂ}

noncomputable def gridCoefficients (X Y : ℕ → ℝ) : ∀ {b}, RectilinearWalk U a b → GridEdgeCoefficients
  | _, .point _ => 0
  | _, .step (z := z) (w := w) p _ _ => gridCoefficients X Y p +
    gridStepCoefficients (readGridIndex X z.re) (readGridIndex Y z.im)
      (readGridIndex X w.re) (readGridIndex Y w.im)

theorem gridDivergence_gridCoefficients (X Y : ℕ → ℝ) (p : RectilinearWalk U a b) (i j : ℕ) :
    gridDivergence (p.gridCoefficients X Y) i j =
      gridIndexMass (readGridIndex X a.re) i * gridIndexMass (readGridIndex Y a.im) j -
      gridIndexMass (readGridIndex X b.re) i * gridIndexMass (readGridIndex Y b.im) j := by
  induction p with
  | point => simp [gridCoefficients,gridDivergence_zero]
  | step p _ _ ih =>
    rw [gridCoefficients,gridDivergence_add,ih,gridDivergence_step]
    ring

theorem gridCoefficients_closed_balance {X Y : ℕ → ℝ} (p : RectilinearWalk U a a) :
    let H := (p.gridCoefficients X Y).1
    let V := (p.gridCoefficients X Y).2
    (∀ i, H i 0 = H (i+1) 0 + V (i+1) 0) ∧
    (∀ i j, H i (j+1) + V (i+1) j = H (i+1) (j+1) + V (i+1) (j+1)) := by
  let H := (p.gridCoefficients X Y).1
  let V := (p.gridCoefficients X Y).2
  have hz (i j : ℕ) : gridDivergence (p.gridCoefficients X Y) i j = 0 := by
    rw [gridDivergence_gridCoefficients,sub_self]
  change (∀ i, H i 0 = H (i+1) 0 + V (i+1) 0) ∧
    (∀ i j, H i (j+1) + V (i+1) j = H (i+1) (j+1) + V (i+1) (j+1))
  refine ⟨fun i => ?_,fun i j => ?_⟩
  · have h := hz (i+1) 0
    change H (i+1) 0 - H i 0 + (V (i+1) 0 - 0) = 0 at h
    linear_combination -h
  · have h := hz (i+1) (j+1)
    change H (i+1) (j+1) - H i (j+1) + (V (i+1) (j+1) - V (i+1) j) = 0 at h
    linear_combination -h

end RectilinearWalk

end SpringerLean
