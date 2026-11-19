import SpringerLean.Round1383ChordArcIdentity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace SpringerLean

theorem coarseArc_b_le_one_twentieth
    (n : ℕ) (hn : 1501 ≤ n) :
    Real.sqrt (3/(n:ℝ)) ≤ 1/20 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hnlarge : (1501:ℝ) ≤ n := by exact_mod_cast hn
  have hsq : (Real.sqrt (3/(n:ℝ)))^2 = 3/(n:ℝ) :=
    Real.sq_sqrt (div_nonneg (by norm_num) hn0.le)
  have hdiv : (3:ℝ)/(n:ℝ) ≤ 1/400 := by
    apply (div_le_iff₀ hn0).2
    nlinarith
  have hroot : 0 ≤ Real.sqrt (3/(n:ℝ)) := Real.sqrt_nonneg _
  nlinarith

/-- On the short chord arc, `2−2cos θ` differs from `θ²` by less than
one per mille. The lower bound is obtained from the cubic sine bound
at the half angle. -/
theorem coarseArc_cos_deficit_quadratic
    (n : ℕ) (hn : 1501 ≤ n) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθb : θ ≤ Real.sqrt (3/(n:ℝ))) :
    (999/1000 : ℝ)*θ^2 ≤ 2-2*Real.cos θ ∧
      2-2*Real.cos θ ≤ θ^2 := by
  have hθsmall : θ ≤ 1/20 := hθb.trans (coarseArc_b_le_one_twentieth n hn)
  have hθsq : θ^2 ≤ 1/400 := by nlinarith [sq_nonneg (θ-1/20)]
  have hθ4 : θ^4 ≤ θ^2/400 := by
    have hθsq0 : 0 ≤ θ^2 := sq_nonneg θ
    nlinarith [mul_nonneg hθsq0 (sub_nonneg.mpr hθsq)]
  have hsin := Real.sin_ge_sub_cube (show 0 ≤ θ/2 by linarith)
  have hsin0 : 0 ≤ Real.sin (θ/2) := Real.sin_nonneg_of_mem_Icc
    ⟨by linarith, by linarith [hθsmall, Real.pi_gt_three]⟩
  have hlow0 : 0 ≤ θ/2-(θ/2)^3/6 := by
    nlinarith [sq_nonneg θ]
  have hsqsin : (θ/2-(θ/2)^3/6)^2 ≤ Real.sin (θ/2)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsin)
      (add_nonneg hsin0 hlow0)]
  have htrig : 2-2*Real.cos θ=4*Real.sin (θ/2)^2 := by
    have hc : Real.cos θ = 2*Real.cos (θ/2)^2-1 := by
      convert Real.cos_two_mul (θ/2) using 1 <;> ring
    have hs := Real.sin_sq_add_cos_sq (θ/2)
    nlinarith
  have hpoly : θ^2-θ^4/12 ≤ 4*(θ/2-(θ/2)^3/6)^2 := by
    nlinarith [sq_nonneg (θ^3)]
  have hnear : (999/1000 : ℝ)*θ^2 ≤ θ^2-θ^4/12 := by
    nlinarith [hθ4]
  constructor
  · rw [htrig]
    nlinarith
  · have hc := Real.one_sub_sq_div_two_le_cos (x := θ)
    nlinarith

end SpringerLean

#print axioms SpringerLean.coarseArc_cos_deficit_quadratic
