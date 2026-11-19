import SpringerLean.Round2091ActualFactorFormula
import SpringerLean.Round2018OddStarConditionalFactorBridge

open MeasureTheory Set

namespace SpringerLean

theorem oddStarRadialFactorFormula_actual (m : ℕ) (hm : 2 ≤ m) :
    OddStarRadialFactorFormula m := by
  intro t ht
  let F := oddStarPerturbation m t
  have hF : CenteredExteriorUnivalent F := oddStarPerturbation_centeredExteriorUnivalent m hm t ht
  obtain ⟨u,v,hu,hv,huv⟩ := (oddStarPerturbation_actual_continuum m hm t ht).2.2.1
  have hμ : oddStarActualBoundaryProbability m t = actualExteriorBoundaryProbability F := by
    unfold oddStarActualBoundaryProbability oddStarAngularProbability actualExteriorBoundaryProbability
      oddStarAngularMeasure actualExteriorBoundaryMeasure F
    rw [Measure.map_smul _ (actualExteriorRadialTrace_aestronglyMeasurable F hF).aemeasurable] <;> rfl
  rw [hμ]
  exact factorConstant_eq_actual_farthest_exp F hF u v hu hv huv

/-- For every odd arm count, an actual nondegenerate rotationally
symmetric plane continuum has greater factor constant than the regular star. -/
theorem odd_regularStar_factorConstant_counterexample
    (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m) :
    ∃ K : Set ℂ, IsCompact K ∧ IsConnected K ∧
      (∃ u v : ℂ, u ∈ K ∧ v ∈ K ∧ u ≠ v) ∧
      (∀ η z : ℂ, η ^ m = 1 → (η * z ∈ K ↔ z ∈ K)) ∧
      factorConstant (regularStarRaySet m) < factorConstant K := by
  have hm2 : 2 ≤ m := by omega
  obtain ⟨t,_,ht,hbetter⟩ := oddStarFactorConstant_strict_of_radialFormula m hm hodd
    (oddStarRadialFactorFormula_actual m hm2)
  rw [oddStarPerturbation_zero_omitted_eq_regularStarRays m hm2] at hbetter
  obtain ⟨hc,hconn,hne,hrot⟩ := oddStarPerturbation_actual_continuum m hm2 t ht
  exact ⟨oddStarPerturbationOmitted m t,hc,hconn,hne,hrot,hbetter⟩

end SpringerLean
