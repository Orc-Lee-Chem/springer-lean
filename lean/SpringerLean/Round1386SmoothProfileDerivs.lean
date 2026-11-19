import SpringerLean.Round1385ArcVariance

namespace SpringerLean

/-- The active branch of the coarse inverse cap, written without a
maximum for differentiation on its short upper arc. -/
noncomputable def coarseSmoothRadius (x : ℝ) : ℝ :=
  (21-Real.sqrt (41-20*x))/10

theorem coarseSmoothRadius_eq_active {x : ℝ}
    (hxlo : (31/16 : ℝ) ≤ x) (hxhi : x ≤ 2) :
    coarseInverseRadius x = coarseSmoothRadius x := by
  rw [coarseInverseRadius_eq_active hxlo hxhi]
  unfold coarseSmoothRadius
  congr 1
  ring

theorem coarseSmoothRadius_hasDerivAt {x : ℝ}
    (hx : x < 41/20) :
    HasDerivAt coarseSmoothRadius
      (1/Real.sqrt (41-20*x)) x := by
  have hA : 0 < 41-20*x := by linarith
  have hAder : HasDerivAt (fun y : ℝ => 41-20*y) (-20) x := by
    have hbase := ((hasDerivAt_id x).const_mul (-20)).const_add 41
    convert hbase using 1
    · funext y; dsimp; ring
    · ring
  have hS := (Real.hasDerivAt_sqrt hA.ne').comp x hAder
  have hroot : Real.sqrt (41-20*x) ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  have hderval : -(1/(2*Real.sqrt (41-20*x))*(-20))/10 =
      1/Real.sqrt (41-20*x) := by
    field_simp [hroot]
    norm_num
  have hb := ((hS.const_sub 21).div_const 10)
  convert hb using 1
  · funext y; dsimp [coarseSmoothRadius]
  · exact hderval.symm

theorem coarseSmoothRadius_deriv {x : ℝ}
    (hx : x < 41/20) :
    deriv coarseSmoothRadius x = 1/Real.sqrt (41-20*x) :=
  (coarseSmoothRadius_hasDerivAt hx).deriv

theorem coarseSmoothRadius_deriv_hasDerivAt {x : ℝ}
    (hx : x < 41/20) :
    HasDerivAt (fun y : ℝ => 1/Real.sqrt (41-20*y))
      (10/(Real.sqrt (41-20*x))^3) x := by
  have hA : 0 < 41-20*x := by linarith
  have hAder : HasDerivAt (fun y : ℝ => 41-20*y) (-20) x := by
    have hbase := ((hasDerivAt_id x).const_mul (-20)).const_add 41
    convert hbase using 1
    · funext y; dsimp; ring
    · ring
  have hS := (Real.hasDerivAt_sqrt hA.ne').comp x hAder
  have hroot : Real.sqrt (41-20*x) ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  convert hS.inv hroot using 1
  · funext y; dsimp; ring
  · field_simp [hroot]
    simp only [Function.comp_apply]
    ring

theorem coarseSmoothRadius_deriv_hasDerivAt' {x : ℝ}
    (hx : x < 41/20) :
    HasDerivAt (deriv coarseSmoothRadius)
      (10/(Real.sqrt (41-20*x))^3) x := by
  have hlocal : ∀ᶠ y in nhds x,
      deriv coarseSmoothRadius y = 1/Real.sqrt (41-20*y) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact coarseSmoothRadius_deriv hy
  exact (coarseSmoothRadius_deriv_hasDerivAt hx).congr_of_eventuallyEq
    (by filter_upwards [hlocal] with y hy; exact hy)

theorem coarseSmoothRadius_second_deriv {x : ℝ}
    (hx : x < 41/20) :
    deriv (deriv coarseSmoothRadius) x =
      10/(Real.sqrt (41-20*x))^3 := by
  exact (coarseSmoothRadius_deriv_hasDerivAt' hx).deriv

theorem coarseSmoothRadius_second_deriv_nonneg {x : ℝ}
    (hx : x < 41/20) : 0 ≤ deriv (deriv coarseSmoothRadius) x := by
  rw [coarseSmoothRadius_second_deriv hx]
  positivity

end SpringerLean

#print axioms SpringerLean.coarseSmoothRadius_hasDerivAt
#print axioms SpringerLean.coarseSmoothRadius_deriv_hasDerivAt
#print axioms SpringerLean.coarseSmoothRadius_second_deriv
