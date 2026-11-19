import SpringerLean.Round1501FlattenedArcLarge

namespace SpringerLean

/-- The centered, mean-preserving flattened cosine profile has exactly
the minimum of the cap-mass and ordinary cosine top integrals at every
proper centered arc. All measures here are raw angle. -/
theorem cappedAngularCosine_arc_integral_eq_min
    {h q : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hq0 : 0 ≤ q) (hqpi : q < Real.pi) :
    (∫ θ in centeredAngularArc q,
      cappedAngularCosine (2*Real.sin h/h) h θ) =
      min (2*q*(2*Real.sin h/h)) (4*Real.sin q) := by
  have hswitch := capped_cosine_top_min_switch
    hh0 hhpi.le hq0 hqpi.le
  by_cases hqh : q ≤ h
  · rw [hswitch,if_pos hqh]
    exact cappedAngularCosine_small_arc_integral hq0 hqh hhpi
  · have hhq : h ≤ q := le_of_lt (lt_of_not_ge hqh)
    have hbalance : 2*h*(2*Real.sin h/h)=4*Real.sin h := by
      field_simp
      ring
    rw [hswitch,if_neg hqh]
    exact cappedAngularCosine_large_arc_integral hh0 hhq hqpi hbalance

end SpringerLean

#print axioms SpringerLean.cappedAngularCosine_arc_integral_eq_min
