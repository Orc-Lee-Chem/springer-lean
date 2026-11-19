import SpringerLean.Round1498RegularizedCappedLevels
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

namespace SpringerLean

/-- The centered cosine arc average decreases with its half-width.
This is the scalar branch test for the mean-preserving flattened model. -/
theorem sine_arc_ratio_le
    {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v)
    (hvpi : v ≤ Real.pi) :
    u*Real.sin v ≤ v*Real.sin u := by
  by_cases hv0 : v = 0
  · have hu : u=0 := by linarith
    simp [hu,hv0]
  have hvpos : 0 < v := lt_of_le_of_ne (hu0.trans huv) (Ne.symm hv0)
  let a : ℝ := u/v
  have ha0 : 0 ≤ a := div_nonneg hu0 hvpos.le
  have ha1 : a ≤ 1 := (div_le_one hvpos).mpr huv
  have hc0 := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0:ℝ) ∈ Set.Icc 0 Real.pi by simp [Real.pi_pos.le])
    (show v ∈ Set.Icc 0 Real.pi by exact ⟨hvpos.le,hvpi⟩)
    (sub_nonneg.mpr ha1) ha0
  have hc := hc0 (by ring : 1-a+a=1)
  simp only [smul_eq_mul] at hc
  have hcomb : (1-a)*0+a*v=u := by
    dsimp [a]
    field_simp
    ring
  rw [hcomb] at hc
  simp only [Real.sin_zero, mul_zero, zero_add] at hc
  have hav : a*v=u := by dsimp [a]; field_simp
  calc
    u*Real.sin v = (a*v)*Real.sin v := by rw [hav]
    _ = (a*Real.sin v)*v := by ring
    _ ≤ (Real.sin u)*v := mul_le_mul_of_nonneg_right hc hvpos.le
    _ = v*Real.sin u := by ring

/-- The cap and cosine top-integral bounds switch at exactly the arc
whose cosine mean equals the endpoint radius. -/
theorem capped_cosine_top_min_switch
    {h q : ℝ} (hh0 : 0 < h) (hhpi : h ≤ Real.pi)
    (hq0 : 0 ≤ q) (hqpi : q ≤ Real.pi) :
    min (2*q*(2*Real.sin h/h)) (4*Real.sin q) =
      if q ≤ h then 2*q*(2*Real.sin h/h) else 4*Real.sin q := by
  by_cases hqh : q ≤ h
  · rw [if_pos hqh, min_eq_left]
    have hs := sine_arc_ratio_le hq0 hqh hhpi
    have heq : 2*q*(2*Real.sin h/h) = (4*q*Real.sin h)/h := by ring
    rw [heq]
    apply (div_le_iff₀ hh0).2
    nlinarith
  · rw [if_neg hqh, min_eq_right]
    have hhq : h ≤ q := le_of_lt (lt_of_not_ge hqh)
    have hs := sine_arc_ratio_le hh0.le hhq hqpi
    have heq : 2*q*(2*Real.sin h/h) = (4*q*Real.sin h)/h := by ring
    rw [heq]
    apply (le_div_iff₀ hh0).2
    nlinarith

end SpringerLean

#print axioms SpringerLean.sine_arc_ratio_le
#print axioms SpringerLean.capped_cosine_top_min_switch
