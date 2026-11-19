import SpringerLean.Round2153GridWalkSupport
import SpringerLean.Round2150GridCauchy

open Set Finset Complex MeasureTheory
open scoped Interval

namespace SpringerLean

private theorem sum_gridSignedSegment_integral_of_le
    {X : ℕ → ℝ} (hX : Monotone X) (N a b : ℕ) (hab : a ≤ b) (hN : b ≤ N)
    (g : ℝ → ℂ) (hg : ContinuousOn g (uIcc (X a) (X b))) :
    ∑ i ∈ range (N+1), gridSignedSegment a b i * (∫ x in X i..X (i+1), g x) =
      ∫ x in X a..X b, g x := by
  have hint : ∀ i ∈ Finset.Ico a b, IntervalIntegrable g volume (X i) (X (i+1)) := by
    intro i hi
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hi
    apply ContinuousOn.intervalIntegrable
    apply hg.mono
    rw [uIcc_of_le (hX hab),uIcc_of_le (hX (Nat.le_succ _))]
    exact Set.Icc_subset_Icc (hX hlo) (hX (by omega))
  calc
    _ = ∑ i ∈ Finset.Ico a b, gridSignedSegment a b i * (∫ x in X i..X (i+1), g x) := by
      symm
      apply Finset.sum_subset (fun i hi => Finset.mem_range.mpr (by
        have h := (Finset.mem_Ico.mp hi).2
        omega))
      intro i _ hi
      rw [show gridSignedSegment a b i = 0 by
        by_cases ha : a ≤ i
        · have hb : b ≤ i := by
            by_contra! h
            exact hi (Finset.mem_Ico.mpr ⟨ha,h⟩)
          exact gridSignedSegment_eq_zero_right ha hb
        · exact gridSignedSegment_eq_zero_left (lt_of_not_ge ha) ((lt_of_not_ge ha).trans_le hab),zero_mul]
    _ = ∑ i ∈ Finset.Ico a b, ∫ x in X i..X (i+1), g x := by
      apply Finset.sum_congr rfl
      intro i hi
      obtain ⟨ha,hb⟩ := Finset.mem_Ico.mp hi
      simp [gridSignedSegment,gridIndexStep,ha,not_le_of_gt hb]
    _ = _ := intervalIntegral.sum_integral_adjacent_intervals_Ico hab
      (fun i hi => hint i (Finset.mem_Ico.mpr hi))

theorem sum_gridSignedSegment_integral
    {X : ℕ → ℝ} (hX : Monotone X) (N a b : ℕ) (ha : a ≤ N) (hb : b ≤ N)
    (g : ℝ → ℂ) (hg : ContinuousOn g (uIcc (X a) (X b))) :
    ∑ i ∈ range (N+1), gridSignedSegment a b i * (∫ x in X i..X (i+1), g x) =
      ∫ x in X a..X b, g x := by
  rcases le_total a b with hab | hba
  · exact sum_gridSignedSegment_integral_of_le hX N a b hab hb g hg
  · have hg' : ContinuousOn g (uIcc (X b) (X a)) := by rwa [Set.uIcc_comm]
    rw [intervalIntegral.integral_symm (X b) (X a),
      ←sum_gridSignedSegment_integral_of_le hX N b a hba ha g hg',←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    unfold gridSignedSegment
    ring

private theorem sum_gridIndexMass_mul (N a : ℕ) (ha : a ≤ N) (g : ℕ → ℂ) :
    ∑ i ∈ range (N+1), gridIndexMass a i * g i = g a := by
  rw [Finset.sum_eq_single a]
  · simp [gridIndexMass]
  · intro i _ hi
    simp [gridIndexMass,Ne.symm hi]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

noncomputable def gridIntegralPairing (X Y : ℕ → ℝ) (N : ℕ) (f : ℂ → ℂ)
    (W : GridEdgeCoefficients) : ℂ :=
  ∑ i ∈ range (N+1), ∑ j ∈ range (N+1),
    (W.1 i j * gridHorizontalIntegral X Y f i j + W.2 i j * gridVerticalIntegral X Y f i j)

theorem gridIntegralPairing_add (X Y : ℕ → ℝ) (N : ℕ) (f : ℂ → ℂ) (W V : GridEdgeCoefficients) :
    gridIntegralPairing X Y N f (W+V) =
      gridIntegralPairing X Y N f W + gridIntegralPairing X Y N f V := by
  simp only [gridIntegralPairing,Prod.fst_add,Prod.snd_add,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  ring

theorem gridIntegralPairing_step
    {X Y : ℕ → ℝ} {N : ℕ} (hX : StrictMono X) (hY : StrictMono Y)
    {f : ℂ → ℂ} {U : Set ℂ} (hf : ContinuousOn f U) {z w : ℂ} (hRect : Rectangle z w ⊆ U)
    (hz : GridPointAtInteriorIndex X Y N z) (hw : GridPointAtInteriorIndex X Y N w) :
    gridIntegralPairing X Y N f
      (gridStepCoefficients (readGridIndex X z.re) (readGridIndex Y z.im)
        (readGridIndex X w.re) (readGridIndex Y w.im)) = wedgeIntegral z w f := by
  let a := readGridIndex X z.re
  let b := readGridIndex Y z.im
  let c := readGridIndex X w.re
  let d := readGridIndex Y w.im
  obtain ⟨_,ha,_,hb,haz,hbz⟩ := hz
  obtain ⟨_,hc,_,hd,hcw,hdw⟩ := hw
  change X a = z.re at haz
  change Y b = z.im at hbz
  change X c = w.re at hcw
  change Y d = w.im at hdw
  let L := gridHorizontalIntegral X Y f
  let M := gridVerticalIntegral X Y f
  have hh : ContinuousOn (fun t : ℝ => f (t+Y b*I)) (uIcc (X a) (X c)) := by
    apply hf.comp (by fun_prop)
    intro t ht
    apply hRect
    simp only [haz,hcw] at ht
    simpa [Rectangle,mem_reProdIm,hbz] using
      (show t ∈ uIcc z.re w.re ∧ z.im ∈ uIcc z.im w.im from ⟨ht,left_mem_uIcc⟩)
  have hv : ContinuousOn (fun t : ℝ => f (X c+t*I)) (uIcc (Y b) (Y d)) := by
    apply hf.comp (by fun_prop)
    intro t ht
    apply hRect
    simp only [hbz,hdw] at ht
    simpa [Rectangle,mem_reProdIm,hcw] using
      (show w.re ∈ uIcc z.re w.re ∧ t ∈ uIcc z.im w.im from ⟨right_mem_uIcc,ht⟩)
  have hH :
      ∑ i ∈ range (N+1), ∑ j ∈ range (N+1), gridIndexMass b j * gridSignedSegment a c i * L i j =
        ∫ x in X a..X c, f (x+Y b*I) := by
    rw [Finset.sum_comm]
    simp only [mul_assoc,←Finset.mul_sum]
    rw [sum_gridIndexMass_mul _ _ hb.le]
    exact sum_gridSignedSegment_integral hX.monotone N a c ha.le hc.le _ hh
  have hV :
      ∑ i ∈ range (N+1), ∑ j ∈ range (N+1), gridIndexMass c i * gridSignedSegment b d j * M i j =
        I * (∫ y in Y b..Y d, f (X c+y*I)) := by
    simp only [mul_assoc,←Finset.mul_sum]
    rw [sum_gridIndexMass_mul _ _ hc.le]
    unfold M gridVerticalIntegral
    simp_rw [mul_left_comm (gridSignedSegment b d _),←Finset.mul_sum]
    rw [sum_gridSignedSegment_integral hY.monotone N b d hb.le hd.le _ hv]
  change (∑ i ∈ range (N+1), ∑ j ∈ range (N+1),
    (gridIndexMass b j * gridSignedSegment a c i * L i j +
      gridIndexMass c i * gridSignedSegment b d j * M i j)) = _
  simp only [Finset.sum_add_distrib,hH,hV,haz,hbz,hcw,hdw,wedgeIntegral,smul_eq_mul]

namespace RectilinearWalk

theorem integral_eq_gridIntegralPairing
    {X Y : ℕ → ℝ} {N : ℕ} (hX : StrictMono X) (hY : StrictMono Y)
    {U : Set ℂ} {f : ℂ → ℂ} (hf : ContinuousOn f U) {a b : ℂ}
    (p : RectilinearWalk U a b)
    (hcoords : ∀ z ∈ p.vertices, GridPointAtInteriorIndex X Y N z) :
    integral f p = gridIntegralPairing X Y N f (p.gridCoefficients X Y) := by
  classical
  induction p with
  | point => simp [integral,gridIntegralPairing,gridCoefficients]
  | @step z w p ax hz ih =>
    have hp (v : ℂ) (hv : v ∈ p.vertices) : GridPointAtInteriorIndex X Y N v :=
      hcoords v (Finset.mem_insert_of_mem hv)
    rw [integral,gridCoefficients,gridIntegralPairing_add,ih hp]
    rw [gridIntegralPairing_step hX hY hf hz (hp z p.target_mem_vertices)
      (hcoords w (Finset.mem_insert_self _ _))]

end RectilinearWalk

end SpringerLean
