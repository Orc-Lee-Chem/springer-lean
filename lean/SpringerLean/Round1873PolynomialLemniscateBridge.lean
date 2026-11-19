import SpringerLean.Round1872ConnectedFiberBridge
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.LocalAtTarget
import Mathlib.Analysis.Convex.PathConnected

open Set Polynomial

namespace SpringerLean

theorem complexPolynomial_isOpenMap_eval (P : ℂ[X]) (hP : 0 < P.natDegree) :
    IsOpenMap P.eval := by
  have han := AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) P
  rcases han.is_constant_or_isOpenMap with ⟨c, hc⟩ | ho
  · have heq : P = C c := by
      apply Polynomial.funext
      intro z
      simpa using hc z
    have hh : P.natDegree = 0 := by rw [heq]; simp
    omega
  · exact ho

/-- A connected set inside a polynomial sublevel set which contains all
zeros already joins every part of that sublevel set.  Properness gives
closedness of the polynomial map; holomorphy gives openness. -/
theorem polynomial_lemniscate_isPreconnected_of_zero_bridge
    (P : ℂ[X]) (hP : 0 < P.natDegree) (R : ℝ) (hR : 0 ≤ R)
    (S : Set ℂ) (hS : IsPreconnected S)
    (hSK : S ⊆ {z : ℂ | ‖P.eval z‖ ≤ R})
    (hzeros : ∀ z : ℂ, P.eval z = 0 → z ∈ S) :
    IsPreconnected {z : ℂ | ‖P.eval z‖ ≤ R} := by
  let D : Set ℂ := Metric.closedBall 0 R
  let K : Set ℂ := P.eval ⁻¹' D
  let f : K → D := fun z => ⟨P.eval (z : ℂ), z.property⟩
  let lift : S → K := fun z => ⟨z, by
    simpa [K, D, Metric.mem_closedBall, dist_zero_right] using hSK z.property⟩
  have hD : IsPreconnected D := (convex_closedBall (0 : ℂ) R).isPreconnected
  haveI : PreconnectedSpace D := Subtype.preconnectedSpace hD
  haveI : PreconnectedSpace S := Subtype.preconnectedSpace hS
  have hcont : Continuous lift := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hbridge : IsPreconnected (Set.range lift) := isPreconnected_range hcont
  have hopen : IsOpenMap f := (complexPolynomial_isOpenMap_eval P hP).restrictPreimage D
  have hclosed : IsClosedMap f := P.isClosedMap_eval.restrictPreimage D
  let y : D := ⟨0, by
    change dist (0 : ℂ) 0 ≤ R
    simpa only [dist_self] using hR⟩
  have hfiber : f ⁻¹' {y} ⊆ Set.range lift := by
    intro z hz
    have hh : f z = y := hz
    have hzero : P.eval (z : ℂ) = 0 := congrArg Subtype.val hh
    have hzS : (z : ℂ) ∈ S := hzeros z hzero
    refine ⟨⟨z, hzS⟩, ?_⟩
    exact Subtype.ext rfl
  haveI : PreconnectedSpace K :=
    preconnectedSpace_of_open_closed_fiber_bridge f hopen hclosed y
      (Set.range lift) hbridge hfiber
  have hK : IsPreconnected K := isPreconnected_iff_preconnectedSpace.2 inferInstance
  simpa only [K, D, Set.preimage_setOf_eq, Metric.closedBall, dist_zero_right] using hK

/-- A directly usable criterion for connected polynomial lemniscates:
the convex hull of all zeros may be used as the joining set. -/
theorem polynomial_lemniscate_isPreconnected_of_zero_hull
    (P : ℂ[X]) (hP : 0 < P.natDegree) (R : ℝ) (hR : 0 ≤ R)
    (hHull : convexHull ℝ {z : ℂ | P.eval z = 0} ⊆
      {z : ℂ | ‖P.eval z‖ ≤ R}) :
    IsPreconnected {z : ℂ | ‖P.eval z‖ ≤ R} := by
  apply polynomial_lemniscate_isPreconnected_of_zero_bridge P hP R hR
    (convexHull ℝ {z : ℂ | P.eval z = 0})
    (convex_convexHull ℝ _).isPreconnected hHull
  intro z hz
  exact subset_convexHull ℝ _ hz

end SpringerLean

#print axioms SpringerLean.polynomial_lemniscate_isPreconnected_of_zero_bridge
#print axioms SpringerLean.polynomial_lemniscate_isPreconnected_of_zero_hull
