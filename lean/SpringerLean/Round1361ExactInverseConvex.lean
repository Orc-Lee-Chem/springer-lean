import SpringerLean.Round1359ExactInverseProfileScalar
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Mul

namespace SpringerLean

private noncomputable def inverseExcess (s : ℝ) : ℝ :=
  s-(Real.sqrt (1+20*s)-1)/10

private theorem inverseExcess_mono_on_nonneg :
    MonotoneOn inverseExcess (Set.Ici (0:ℝ)) := by
  intro s hs t ht hst
  change 0 ≤ s at hs
  change 0 ≤ t at ht
  have hsa : 1 ≤ Real.sqrt (1+20*s) := by
    have h : 1 ≤ 1+20*s := by linarith
    simpa using Real.sqrt_le_sqrt h
  have hta : 1 ≤ Real.sqrt (1+20*t) := by
    have h : 1 ≤ 1+20*t := by linarith
    simpa using Real.sqrt_le_sqrt h
  have hroot : Real.sqrt (1+20*s) ≤ Real.sqrt (1+20*t) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsSq : (Real.sqrt (1+20*s))^2 = 1+20*s :=
    Real.sq_sqrt (by linarith)
  have htSq : (Real.sqrt (1+20*t))^2 = 1+20*t :=
    Real.sq_sqrt (by linarith)
  have hprod : 0 ≤ (Real.sqrt (1+20*t)-Real.sqrt (1+20*s))*
      (Real.sqrt (1+20*t)+Real.sqrt (1+20*s)-2) :=
    mul_nonneg (by linarith) (by linarith)
  dsimp [inverseExcess]
  nlinarith

private theorem inverseExcess_convex_on_nonneg :
    ConvexOn ℝ (Set.Ici (0:ℝ)) inverseExcess := by
  refine ⟨convex_Ici _, ?_⟩
  intro s hs t ht a b ha hb hab
  change 0 ≤ s at hs
  change 0 ≤ t at ht
  have hsa : 0 ≤ 1+20*s := by linarith
  have hta : 0 ≤ 1+20*t := by linarith
  have hroot := (Real.strictConcaveOn_sqrt.concaveOn).2 hsa hta ha hb hab
  have harg : 1+20*(a*s+b*t) = a*(1+20*s)+b*(1+20*t) := by
    calc
      1+20*(a*s+b*t) = (a+b)+20*(a*s+b*t) := by rw [hab]
      _ = a*(1+20*s)+b*(1+20*t) := by ring
  simp only [smul_eq_mul, Function.comp_apply] at hroot ⊢
  rw [← harg] at hroot
  dsimp [inverseExcess]
  nlinarith

private theorem inverseHinge_convexOn :
    ConvexOn ℝ Set.univ
      (fun x : ℝ => max (0:ℝ) (2-x)) := by
  have hlin : ConvexOn ℝ Set.univ (fun x : ℝ => 2-x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ hab
    dsimp
    apply le_of_eq
    calc
      (2:ℝ)-(a*x+b*y) = (a+b)*2-(a*x+b*y) := by rw [hab]; ring
      _ = a*(2-x)+b*(2-y) := by ring
  convert (convexOn_const (0:ℝ) convex_univ).sup hlin using 1

private theorem inverseExcess_hinge_convexOn :
    ConvexOn ℝ Set.univ
      (fun x : ℝ => inverseExcess (max (0:ℝ) (2-x))) := by
  have himage : (fun x : ℝ => max (0:ℝ) (2-x)) '' Set.univ =
      Set.Ici (0:ℝ) := by
    ext y
    constructor
    · rintro ⟨x,_,rfl⟩
      change (0:ℝ) ≤ max 0 (2-x)
      exact le_max_left _ _
    · intro hy
      change 0 ≤ y at hy
      refine ⟨2-y, Set.mem_univ _, ?_⟩
      simpa [max_eq_right hy]
  have hconv : ConvexOn ℝ
      ((fun x : ℝ => max (0:ℝ) (2-x)) '' Set.univ) inverseExcess := by
    rw [himage]
    exact inverseExcess_convex_on_nonneg
  have hmono : MonotoneOn inverseExcess
      ((fun x : ℝ => max (0:ℝ) (2-x)) '' Set.univ) := by
    rw [himage]
    exact inverseExcess_mono_on_nonneg
  have hcomp := hconv.comp inverseHinge_convexOn hmono
  simpa only [Function.comp_def] using hcomp

private theorem coarseInverseRadius_eq_convex_form (x : ℝ) :
    coarseInverseRadius x =
      max (39/20 : ℝ) (x+inverseExcess (max (0:ℝ) (2-x))) := by
  by_cases hx : x ≤ 2
  · have hhinge : max (0:ℝ) (2-x) = 2-x := max_eq_right (by linarith)
    simp only [coarseInverseRadius, if_pos hx, hhinge, inverseExcess]
    congr 1
    ring
  · have hx' : 2 < x := lt_of_not_ge hx
    have hhinge : max (0:ℝ) (2-x) = 0 := max_eq_left (by linarith)
    have hzero : inverseExcess 0 = 0 := by
      simp [inverseExcess]
    simp [coarseInverseRadius, hx, hhinge, hzero,
      max_eq_right (by linarith : (39/20:ℝ) ≤ x)]

/-- The exact inverse-square-root radius profile is a globally convex
test, so it can be used with the actual finite convex-cap theorem. -/
theorem coarseInverseRadius_convexOn :
    ConvexOn ℝ Set.univ coarseInverseRadius := by
  have hsum : ConvexOn ℝ Set.univ
      (fun x : ℝ => x+inverseExcess (max (0:ℝ) (2-x))) :=
    (convexOn_id convex_univ).add inverseExcess_hinge_convexOn
  have hmax := (convexOn_const (39/20 : ℝ) convex_univ).sup hsum
  convert hmax using 1
  funext x
  exact coarseInverseRadius_eq_convex_form x

theorem coarseInverseRadius_ge_platform (x : ℝ) :
    (39/20 : ℝ) ≤ coarseInverseRadius x := by
  by_cases hx : x ≤ 2
  · exact coarseInverseRadius_ge_platform_of_le_two hx
  · have hx' : 2 < x := lt_of_not_ge hx
    simp only [coarseInverseRadius, if_neg hx]
    linarith

theorem coarseInverseRadius_pos (x : ℝ) : 0 < coarseInverseRadius x :=
  lt_of_lt_of_le (by norm_num : (0:ℝ) < 39/20)
    (coarseInverseRadius_ge_platform x)

theorem coarseInverseRadius_mono : Monotone coarseInverseRadius := by
  intro x y hxy
  by_cases hy2 : y ≤ 2
  · have hx2 : x ≤ 2 := hxy.trans hy2
    have hroot : Real.sqrt (1+20*(2-y)) ≤
        Real.sqrt (1+20*(2-x)) :=
      Real.sqrt_le_sqrt (by linarith)
    simp only [coarseInverseRadius, if_pos hx2, if_pos hy2]
    exact max_le_max_left _ (by linarith)
  · have hy2' : 2 < y := lt_of_not_ge hy2
    by_cases hx2 : x ≤ 2
    · have harg : 1 ≤ 1+20*(2-x) := by linarith
      have hroot : 1 ≤ Real.sqrt (1+20*(2-x)) := by
        simpa using Real.sqrt_le_sqrt harg
      have hraw : 2-(Real.sqrt (1+20*(2-x))-1)/10 ≤ 2 := by
        linarith
      simp only [coarseInverseRadius, if_pos hx2, if_neg hy2]
      exact (max_le (by norm_num) hraw).trans hy2'.le
    · simp only [coarseInverseRadius, if_neg hx2, if_neg hy2]
      exact hxy

theorem coarseInverseRadius_pow_convexOn (n : ℕ) :
    ConvexOn ℝ Set.univ (fun x => coarseInverseRadius x ^ n) := by
  convert (coarseInverseRadius_convexOn.pow
    (fun x _ => le_trans (by norm_num : (0:ℝ) ≤ 39/20)
      (coarseInverseRadius_ge_platform x)) n) using 1

end SpringerLean

#print axioms SpringerLean.coarseInverseRadius_convexOn
#print axioms SpringerLean.coarseInverseRadius_pow_convexOn
