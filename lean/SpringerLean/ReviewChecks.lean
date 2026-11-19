import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace SpringerAnalyticReview

/-- Uniform-arc constants for the variance and the raw cubic difference. -/
theorem arcMomentConstants :
    (199/200:ℝ)*(4/45) < (999/1000:ℝ)^2/5-1/9 ∧
    (1/7:ℝ)-(999/1000:ℝ)^3/27 < (6/5:ℝ)*(199/200)*(4/45) := by
  constructor <;> norm_num

theorem rawCubicGap (b V T : ℝ)
    (hV : (199/200:ℝ)*(4/45)*b^4 ≤ V)
    (hT : T ≤ (1/7-(999/1000:ℝ)^3/27)*b^6) :
    T ≤ 3*(2*b^2/5)*V := by
  have h₁ := mul_le_mul_of_nonneg_right arcMomentConstants.2.le
    (show 0 ≤ b^6 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hV (sq_nonneg b)
  nlinarith

theorem cubicJensen (B s₀ V T : ℝ) (hB : 0 ≤ B) (hT : T ≤ 3*s₀*V) :
    V/2 ≤ (1+B*s₀)*V/2-B*T/6 := by
  nlinarith [mul_le_mul_of_nonneg_left hT hB]

theorem coefficientFloor :
    (67/1000:ℝ) < (173/100)/(8*(22/7))*(199/200)*(1500/1501)*
      (1-(107/100)/500)^2 := by norm_num

/-- With w=mW, e=m(R-x) and Y=m Im(conj ξ z), this bounds the tangent,
    which enters the radial logarithm itself. -/
theorem tangentFromStrip (w e Y x s : ℝ)
    (hw : 0 ≤ w) (hw' : w ≤ 1/2) (he : e ≤ 2*s)
    (hs : 0 ≤ s) (hx : 9/5 ≤ x)
    (strip : Y^2 ≤ 4*w*(w+e)) :
    Y^2/(2*x^2) ≤ 1/6+5*s/8 := by
  have h₁ := mul_le_mul_of_nonneg_left (add_le_add hw' he) hw
  have h₂ := mul_le_mul_of_nonneg_right hw' (show 0 ≤ 1/2+2*s by linarith)
  have h₃ := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 9/5) hx 2
  have h₄ := mul_le_mul_of_nonneg_left h₃ (show (0:ℝ) ≤ 1/6+5*s/8 by linarith)
  have hxpos : 0 < x := by linarith
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 2) (pow_pos hxpos 2))).2
  nlinarith

/-- Homogenize the one-variable flux bound, including p=0. -/
theorem homogeneousFlux (a b d k u p : ℝ) (ha : 0 ≤ a)
    (hk : 0 ≤ k) (hp : 0 ≤ p)
    (H : ∀ q : ℝ, 0 ≤ q → d+b*q-a*q^2 ≤ 7/3) :
    d*p^2+k*b*|u| *p-k^2*a*u^2 ≤ (7/3)*p^2 := by
  rcases eq_or_lt_of_le hp with hz | hpos
  · subst p
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub]
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (sq_nonneg k) ha) (sq_nonneg u))
  · have hq := H (k*|u|/p) (div_nonneg (mul_nonneg hk (abs_nonneg u)) hpos.le)
    have he := mul_le_mul_of_nonneg_right hq (sq_nonneg p)
    have hid : (d+b*(k*|u|/p)-a*(k*|u|/p)^2)*p^2 =
        d*p^2+k*b*|u| *p-k^2*a*u^2 := by
      field_simp [ne_of_gt hpos]
      rw [sq_abs]
      ring
    rw [hid] at he
    exact he

#print axioms arcMomentConstants
#print axioms rawCubicGap
#print axioms cubicJensen
#print axioms coefficientFloor
#print axioms tangentFromStrip
#print axioms homogeneousFlux
end SpringerAnalyticReview
