import SpringerLean.Round1389PowerLower

namespace SpringerLean

theorem coarseSmoothRadius_ge_projection
    {x : ℝ} (hxlo : (31/16 : ℝ) ≤ x) (hxhi : x ≤ 2) :
    x ≤ coarseSmoothRadius x := by
  let s : ℝ := 2-x
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hA : 0 ≤ 41-20*x := by dsimp [s] at hs; linarith
  have hrootSq := Real.sq_sqrt hA
  have hbound : 41-20*x ≤ (1+10*s)^2 := by
    dsimp [s]
    nlinarith [sq_nonneg (2-x)]
  have hroot : Real.sqrt (41-20*x) ≤ 1+10*s := by
    have hright : 0 ≤ 1+10*s := by linarith
    nlinarith [sq_nonneg (Real.sqrt (41-20*x) - (1+10*s))]
  unfold coarseSmoothRadius
  dsimp [s] at hroot
  linarith

theorem coarseSmoothRadius_arc_lower
    (n : ℕ) (hn : 1501 ≤ n) {x : ℝ}
    (hxlo : 2*Real.cos (Real.sqrt (3/(n:ℝ))) ≤ x)
    (hxhi : x ≤ 2) :
    2-3/(n:ℝ) ≤ coarseSmoothRadius x := by
  let b : ℝ := Real.sqrt (3/(n:ℝ))
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hbS := (coarseArc_cos_deficit_quadratic n hn hb0 (le_refl b)).2
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hb2 : b^2=3/(n:ℝ) := Real.sq_sqrt (div_nonneg (by norm_num) hn0.le)
  have hxlower : 2-3/(n:ℝ) ≤ x := by
    dsimp [b] at hxlo hbS hb2
    linarith
  have hactiveLo : (31/16 : ℝ) ≤ x := by
    have hnlarge : (1501:ℝ) ≤ n := by exact_mod_cast hn
    have hfrac : 3/(n:ℝ) ≤ 1/16 :=
      (div_le_iff₀ hn0).2 (by nlinarith)
    linarith
  exact hxlower.trans (coarseSmoothRadius_ge_projection hactiveLo hxhi)

theorem coarseSmoothRadius_arc_deriv_sq_lower
    (n : ℕ) (hn : 1501 ≤ n) {x : ℝ}
    (hxlo : 2*Real.cos (Real.sqrt (3/(n:ℝ))) ≤ x)
    (hxhi : x ≤ 2) :
    (9/10 : ℝ) ≤ (deriv coarseSmoothRadius x)^2 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hnlarge : (1501:ℝ) ≤ n := by exact_mod_cast hn
  let b : ℝ := Real.sqrt (3/(n:ℝ))
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hbS := (coarseArc_cos_deficit_quadratic n hn hb0 (le_refl b)).2
  have hb2 : b^2=3/(n:ℝ) := Real.sq_sqrt (div_nonneg (by norm_num) hn0.le)
  have hs : 0 ≤ 2-x ∧ 2-x ≤ 3/(n:ℝ) := by
    dsimp [b] at hxlo hbS hb2
    constructor <;> linarith
  have hApos : 0 < 41-20*x := by linarith [hs.1]
  have hAupper : 41-20*x ≤ 10/9 := by
    have h60 : (60:ℝ)/(n:ℝ) ≤ 1/9 :=
      (div_le_iff₀ hn0).2 (by nlinarith)
    have hscaled : 20*(2-x) ≤ 60/(n:ℝ) := by
      convert mul_le_mul_of_nonneg_left hs.2 (by norm_num : (0:ℝ) ≤ 20) using 1 <;> ring
    linarith
  have hxA : x < 41/20 := by linarith
  rw [coarseSmoothRadius_deriv hxA]
  have hsq : (Real.sqrt (41-20*x))^2=41-20*x :=
    Real.sq_sqrt hApos.le
  have hrootNe : Real.sqrt (41-20*x) ≠ 0 :=
    (Real.sqrt_pos.2 hApos).ne'
  have heq : (1/Real.sqrt (41-20*x))^2 = 1/(41-20*x) := by
    rw [one_div, inv_pow, ← one_div, hsq]
  rw [heq]
  exact (le_div_iff₀ hApos).2 (by nlinarith [hAupper])

end SpringerLean

#print axioms SpringerLean.coarseSmoothRadius_arc_lower
#print axioms SpringerLean.coarseSmoothRadius_arc_deriv_sq_lower
