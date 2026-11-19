import SpringerLean.Round1396ProjectionVariance
import Mathlib.Analysis.Real.Pi.Bounds

namespace SpringerLean

theorem coarseArc_relative_saving_gt_centipercent
    (n : ℕ) (hn : 1501 ≤ n) :
    (1/100 : ℝ) <
      (Real.sqrt 3/(50*Real.pi))*(99/100 : ℝ)*(1-1/(n:ℝ)) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hnlarge : (1501:ℝ) ≤ n := by exact_mod_cast hn
  have hq : (99/100 : ℝ) < 1-1/(n:ℝ) := by
    have hfrac : 1/(n:ℝ) < 1/100 :=
      (div_lt_div_iff₀ hn0 (by norm_num : (0:ℝ)<100)).2 (by nlinarith)
    linarith
  have hroot : (17/10 : ℝ) < Real.sqrt 3 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    have hp := Real.sqrt_nonneg 3
    nlinarith
  have hroot0 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hπ : Real.pi < 22/7 := by
    have hh := Real.pi_lt_d20
    norm_num at hh ⊢
    linarith
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have hprod : (17/10 : ℝ)*(99/100)^2 <
      Real.sqrt 3*(99/100)*(1-1/(n:ℝ)) := by
    calc
      (17/10 : ℝ)*(99/100)^2 < Real.sqrt 3*(99/100)^2 :=
        mul_lt_mul_of_pos_right hroot (by norm_num)
      _ = (Real.sqrt 3*(99/100))*(99/100) := by ring
      _ < (Real.sqrt 3*(99/100))*(1-1/(n:ℝ)) :=
        mul_lt_mul_of_pos_left hq (by positivity)
      _ = _ := by ring
  have htarget : Real.pi/2 <
      Real.sqrt 3*(99/100)*(1-1/(n:ℝ)) := by
    have hrat : (22/7 : ℝ)/2 < (17/10 : ℝ)*(99/100)^2 := by norm_num
    linarith
  calc
    (1/100 : ℝ) = (Real.pi/2)/(50*Real.pi) := by
      field_simp [hπ0.ne']
      ring
    _ < (Real.sqrt 3*(99/100)*(1-1/(n:ℝ)))/(50*Real.pi) :=
      div_lt_div_of_pos_right htarget (by positivity)
    _ = (Real.sqrt 3/(50*Real.pi))*(99/100)*(1-1/(n:ℝ)) := by ring

end SpringerLean

#print axioms SpringerLean.coarseArc_relative_saving_gt_centipercent
