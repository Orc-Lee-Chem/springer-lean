import SpringerLean.Round1517PowerTangentGap
import Mathlib.Analysis.Convex.Piecewise

namespace SpringerLean
set_option maxHeartbeats 320000

/-- The ordinary positive-part integer power is convex on the whole
real line. This is the left branch of the clipped tangent test. -/
theorem positivePart_pow_convexOn (m : ℕ) (hm : 1 ≤ m) :
    ConvexOn ℝ Set.univ (fun x : ℝ => (max x 0)^m) := by
  have hleft : ConvexOn ℝ (Set.Iic (0:ℝ)) (fun _ : ℝ => (0:ℝ)) :=
    convexOn_const 0 (convex_Iic 0)
  have hright : ConvexOn ℝ (Set.Ici (0:ℝ)) (fun x : ℝ => x^m) :=
    convexOn_pow m
  have hleftAnti : AntitoneOn (fun _ : ℝ => (0:ℝ)) (Set.Iic (0:ℝ)) :=
    fun _ _ _ _ _ => le_refl _
  have hrightMono : MonotoneOn (fun x : ℝ => x^m) (Set.Ici (0:ℝ)) :=
    pow_left_monotoneOn
  have hm0 : 0 < m := by omega
  have hmne : m ≠ 0 := by omega
  have hglue := convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici
    hleft hright hleftAnti hrightMono (by simp [hmne])
  convert hglue using 1
  funext x
  by_cases hx : x ≤ 0
  · simp [Set.piecewise, hx, max_eq_right hx, hmne]
  · have hx0 : 0 < x := lt_of_not_ge hx
    simp [Set.piecewise, hx, max_eq_left hx0.le]

end SpringerLean

#print axioms SpringerLean.positivePart_pow_convexOn
