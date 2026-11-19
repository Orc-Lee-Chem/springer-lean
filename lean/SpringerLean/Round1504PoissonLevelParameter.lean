import SpringerLean.Round1503CappedPoissonLevels
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

open Set

namespace SpringerLean

/-- Every proper positive centered Poisson superlevel has the same
centered arc parameter as the cosine comparator. -/
theorem centeredPoisson_proper_level_eq_arc
    {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ht : 0 < t)
    (a : ℝ)
    (ha : a = ((1+r^2)*t-(1-r^2))/(r*t))
    (haLo : -2 < a) (haHi : a ≤ 2) :
    let q := Real.arccos (a/2)
    0 ≤ q ∧ q < Real.pi ∧
      (Ioc (0:ℝ) (2*Real.pi) ∩
        {θ : ℝ | t ≤ poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)}) =
        centeredAngularArc q := by
  let q : ℝ := Real.arccos (a/2)
  have hq0 : 0 ≤ q := Real.arccos_nonneg _
  have hqpi : q < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
  have hcos : 2*Real.cos q = a := by
    dsimp [q]
    rw [Real.cos_arccos (by linarith) (by linarith)]
    ring
  refine ⟨hq0,hqpi,?_⟩
  calc
    (Ioc (0:ℝ) (2*Real.pi) ∩
      {θ : ℝ | t ≤ poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)}) =
        (Ioc (0:ℝ) (2*Real.pi) ∩
          {θ : ℝ | 2*Real.cos q ≤ 2*Real.cos θ}) := by
            ext θ
            simp only [mem_inter_iff,mem_setOf_eq]
            rw [centeredPoisson_superlevel_iff_comparator_superlevel hr0 hr1 ht]
            rw [← ha,← hcos]
    _ = centeredAngularArc q := by
      convert comparator_superlevel_inter_turn_eq_centeredAngularArc
        q hq0 hqpi.le using 1
      simp [circleMap_zero_re]

/-- A kernel threshold above the cosine range has an empty one-turn
superlevel. -/
theorem centeredPoisson_level_empty_of_high_threshold
    {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ht : 0 < t)
    (a : ℝ) (ha : a = ((1+r^2)*t-(1-r^2))/(r*t))
    (haHi : 2 < a) :
    (Ioc (0:ℝ) (2*Real.pi) ∩
      {θ : ℝ | t ≤ poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)}) = ∅ := by
  ext θ
  simp only [mem_inter_iff,mem_setOf_eq,mem_empty_iff_false,iff_false]
  rintro ⟨_,hθ⟩
  have hcomp := (centeredPoisson_superlevel_iff_comparator_superlevel
    hr0 hr1 ht θ).mp hθ
  rw [←ha] at hcomp
  nlinarith [Real.cos_le_one θ]

/-- A kernel threshold below the cosine range covers the entire turn. -/
theorem centeredPoisson_level_full_of_low_threshold
    {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ht : 0 < t)
    (a : ℝ) (ha : a = ((1+r^2)*t-(1-r^2))/(r*t))
    (haLo : a ≤ -2) :
    (Ioc (0:ℝ) (2*Real.pi) ∩
      {θ : ℝ | t ≤ poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)}) =
      Ioc (0:ℝ) (2*Real.pi) := by
  ext θ
  simp only [mem_inter_iff,mem_setOf_eq]
  constructor
  · exact And.left
  · intro hθ
    refine ⟨hθ,?_⟩
    apply (centeredPoisson_superlevel_iff_comparator_superlevel
      hr0 hr1 ht θ).2
    rw [←ha]
    nlinarith [Real.neg_one_le_cos θ]

end SpringerLean

#print axioms SpringerLean.centeredPoisson_proper_level_eq_arc
#print axioms SpringerLean.centeredPoisson_level_empty_of_high_threshold
#print axioms SpringerLean.centeredPoisson_level_full_of_low_threshold
