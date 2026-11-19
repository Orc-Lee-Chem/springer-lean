import SpringerLean.Round1446MovingChordSaving
import Mathlib.Analysis.Real.Pi.Bounds

namespace SpringerLean

/-- The rational reserve after the cosine-moment bound, short-arc
variance bound, and minimum affine slope. The exponential reserve is
not needed for this scalar comparison. -/
theorem refinedAffine_moving_saving_constant :
    (67/1000:ℝ) <
      (Real.sqrt 3/(8*Real.pi))*(995/1000)*(1500/1501)*
        ((49893/50000:ℝ)^2) := by
  have hroot : (173/100:ℝ) < Real.sqrt 3 := by
    have hs : (Real.sqrt 3)^2=(3:ℝ) := Real.sq_sqrt (by norm_num)
    have hnonneg := Real.sqrt_nonneg (3:ℝ)
    nlinarith
  have hpi : Real.pi < (31416/10000:ℝ) := by
    convert Real.pi_lt_d4 using 1 <;> norm_num
  have hpipos : 0 < Real.pi := Real.pi_pos
  have hrat :
      (67/1000:ℝ)*8*(31416/10000) <
      (173/100)*(995/1000)*(1500/1501)*
        ((49893/50000:ℝ)^2) := by norm_num
  have hgoal : (67/1000:ℝ) <
      (Real.sqrt 3*(995/1000)*(1500/1501)*
        ((49893/50000:ℝ)^2))/(8*Real.pi) := by
    apply (lt_div_iff₀ (by positivity : 0 < 8*Real.pi)).2
    nlinarith
  convert hgoal using 1 <;> ring

end SpringerLean

#print axioms SpringerLean.refinedAffine_moving_saving_constant
