import SpringerLean.Round1366ExactChordProfile
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace SpringerLean

/-- The arc mean for the first bad-deficit chord lies above the radius
cap `2-1/n` and strictly to the right of the arc endpoint. -/
theorem coarseArc_mean_bounds
    (n : ℕ) (hn : 1501 ≤ n) :
    let b : ℝ := Real.sqrt (3/(n:ℝ))
    let x₀ : ℝ := 2*Real.cos b
    let μ : ℝ := 2*Real.sin b/b
    0 < b ∧ x₀ < μ ∧ 2-1/(n:ℝ) ≤ μ ∧ μ ≤ 2 := by
  dsimp
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hn1501 : (1501:ℝ) ≤ n := by exact_mod_cast hn
  have hfrac : 0 < (3:ℝ)/(n:ℝ) := div_pos (by norm_num) hn0
  have hb : 0 < Real.sqrt (3/(n:ℝ)) := Real.sqrt_pos.2 hfrac
  let b : ℝ := Real.sqrt (3/(n:ℝ))
  have hb2 : b^2 = 3/(n:ℝ) := Real.sq_sqrt hfrac.le
  have hbSmall : b ≤ 1 := by
    have hfrac1 : (3:ℝ)/(n:ℝ) ≤ 1 := by
      apply (div_le_iff₀ hn0).2
      linarith
    nlinarith [hb2]
  have hbpi : |b| ≤ Real.pi := by
    rw [abs_of_pos hb]
    linarith [Real.pi_gt_three]
  have hsin := Real.sin_gt_sub_cube hb
  have hcos := Real.cos_le_one_sub_mul_cos_sq hbpi
  have hpi : Real.pi^2 < 10 := by
    have hpipos : 0 < Real.pi := Real.pi_pos
    have hpi3 := Real.pi_lt_d2
    nlinarith [sq_nonneg (Real.pi-(315/100 : ℝ))]
  have hpic : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have hcosWeak : Real.cos b ≤ 1-b^2/5 := by
    have hcoef : (1/5 : ℝ) ≤ 2/Real.pi^2 := by
      apply (le_div_iff₀ hpic).2
      linarith
    have hb2nonneg : 0 ≤ b^2 := sq_nonneg b
    nlinarith [mul_le_mul_of_nonneg_right hcoef hb2nonneg]
  have hsinDiv : 1-b^2/6 < Real.sin b/b := by
    apply (lt_div_iff₀ hb).2
    nlinarith [hsin]
  have hmeanLower : 2-1/(n:ℝ) < 2*Real.sin b/b := by
    have hdiv : b^2/3 = 1/(n:ℝ) := by
      rw [hb2]
      ring
    have htwo : 2*(Real.sin b/b) = 2*Real.sin b/b := by ring
    rw [← htwo]
    linarith
  have hx0mean : 2*Real.cos b < 2*Real.sin b/b := by
    have hbpos2 : 0 < b^2 := sq_pos_of_pos hb
    have htwo : 2*(Real.sin b/b) = 2*Real.sin b/b := by ring
    rw [← htwo]
    linarith
  have hsinLe := Real.sin_le hb.le
  have hmeanUpper : 2*Real.sin b/b ≤ 2 := by
    apply (div_le_iff₀ hb).2
    nlinarith
  exact ⟨hb,hx0mean,hmeanLower.le,hmeanUpper⟩

end SpringerLean

#print axioms SpringerLean.coarseArc_mean_bounds
