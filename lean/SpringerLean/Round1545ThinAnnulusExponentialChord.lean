import SpringerLean.Round1544SelectedTwoCirclePeakSavings
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace SpringerLean
set_option maxHeartbeats 320000

/-- Convexity of the exponential gives a linear lower bound on the
missing radial mass; no series is used in this interpolation step. -/
theorem one_sub_exp_neg_mul_chord
    {a x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x*(1-Real.exp (-a)) ≤ 1-Real.exp (-a*x) := by
  have hcv := convexOn_exp.2 (Set.mem_univ (-a))
    (Set.mem_univ (0:ℝ)) hx0 (sub_nonneg.mpr hx1)
    (show x+(1-x)=1 by ring)
  have hraw : Real.exp (-a*x) ≤
      x*Real.exp (-a)+(1-x) := by
    convert hcv using 1 <;> simp [smul_eq_mul] <;> ring
  linarith

private theorem exp_nine_fourths_gt_nine :
    (9:ℝ) < Real.exp (9/4) := by
  have hE1 : (27/10:ℝ) < Real.exp 1 := by
    have hp := Real.exp_one_gt_d9
    norm_num at hp ⊢
    linarith
  have hE2 : (27/10:ℝ)^2 < Real.exp 2 := by
    rw [show (2:ℝ)=1+1 by ring,Real.exp_add]
    nlinarith [hE1,Real.exp_pos (1:ℝ)]
  have hE4 : (5/4:ℝ) ≤ Real.exp (1/4) := by
    linarith [Real.add_one_le_exp (1/4:ℝ)]
  calc
    (9:ℝ) < (27/10:ℝ)^2*(5/4) := by norm_num
    _ < Real.exp 2*(5/4) :=
      mul_lt_mul_of_pos_right hE2 (by norm_num)
    _ ≤ Real.exp 2*Real.exp (1/4) :=
      mul_le_mul_of_nonneg_left hE4 (Real.exp_pos _).le
    _ = Real.exp (9/4) := by rw [←Real.exp_add]; ring

private theorem exp_nine_tenths_gt_fifteen_sevenths :
    (15/7:ℝ) < Real.exp (9/10) := by
  have hE1 : (27/10:ℝ) < Real.exp 1 := by
    have hp := Real.exp_one_gt_d9
    norm_num at hp ⊢
    linarith
  have hEn : (9/10:ℝ) ≤ Real.exp (-1/10) := by
    linarith [Real.add_one_le_exp (-1/10:ℝ)]
  calc
    (15/7:ℝ) < (27/10:ℝ)*(9/10) := by norm_num
    _ < Real.exp 1*(9/10) :=
      mul_lt_mul_of_pos_right hE1 (by norm_num)
    _ ≤ Real.exp 1*Real.exp (-1/10) :=
      mul_le_mul_of_nonneg_left hEn (Real.exp_pos _).le
    _ = Real.exp (9/10) := by rw [←Real.exp_add]; ring

/-- On [0,1], the outer-annulus exponential loss is at least 8x/9. -/
theorem thinAnnulus_exp_loss_general
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (8/9:ℝ)*x ≤ 1-Real.exp (-(9/4)*x) := by
  have hneg : Real.exp (-(9/4:ℝ)) < 1/9 := by
    rw [Real.exp_neg,inv_eq_one_div]
    exact (div_lt_div_iff₀ (Real.exp_pos _) (by norm_num : (0:ℝ)<9)).2
      (by nlinarith [exp_nine_fourths_gt_nine])
  have hc := one_sub_exp_neg_mul_chord (a:=9/4) hx0 hx1
  nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hneg.le)]

/-- On [0,2/5], the same chord yields the stronger 4x/3 loss. -/
theorem thinAnnulus_exp_loss_small
    {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2/5) :
    (4/3:ℝ)*x ≤ 1-Real.exp (-(9/4)*x) := by
  have ht0 : 0 ≤ (5/2:ℝ)*x := by positivity
  have ht1 : (5/2:ℝ)*x ≤ 1 := by nlinarith [hx2]
  have hneg : Real.exp (-(9/10:ℝ)) < 7/15 := by
    rw [Real.exp_neg,inv_eq_one_div]
    exact (div_lt_div_iff₀ (Real.exp_pos _) (by norm_num : (0:ℝ)<15)).2
      (by nlinarith [exp_nine_tenths_gt_fifteen_sevenths])
  have hc := one_sub_exp_neg_mul_chord (a:=9/10) ht0 ht1
  have harg : -(9/10:ℝ)*((5/2)*x)=-(9/4:ℝ)*x := by ring
  rw [harg] at hc
  nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hneg.le)]

end SpringerLean

#print axioms SpringerLean.one_sub_exp_neg_mul_chord
#print axioms SpringerLean.thinAnnulus_exp_loss_general
#print axioms SpringerLean.thinAnnulus_exp_loss_small
