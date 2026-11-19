import SpringerLean.Round1943OddStarSeedOmittedCurve
import SpringerLean.Round1873PolynomialLemniscateBridge

open Set Polynomial

namespace SpringerLean

/-- The full preimage of a preconnected plane set containing zero under a
positive integer power is preconnected. The ramified fiber over zero joins
the sheets of the open and closed polynomial map. -/
theorem power_preimage_isPreconnected_of_zero_mem
    (m : ℕ) (hm : 0 < m) (E : Set ℂ)
    (hE : IsPreconnected E) (hzero : (0 : ℂ) ∈ E) :
    IsPreconnected {z : ℂ | z ^ m ∈ E} := by
  let P : ℂ[X] := X ^ m
  have hdegree : 0 < P.natDegree := by
    simp [P, natDegree_pow]
    omega
  have heval : P.eval = (fun z : ℂ => z ^ m) := by
    funext z
    simp [P]
  have hopen0 : IsOpenMap (fun z : ℂ => z ^ m) := by
    rw [← heval]
    exact complexPolynomial_isOpenMap_eval P hdegree
  have hclosed0 : IsClosedMap (fun z : ℂ => z ^ m) := by
    rw [← heval]
    exact P.isClosedMap_eval
  let K : Set ℂ := (fun z : ℂ => z ^ m) ⁻¹' E
  let f : K → E := fun z => ⟨(z : ℂ) ^ m, z.property⟩
  letI : PreconnectedSpace E := Subtype.preconnectedSpace hE
  have hopen : IsOpenMap f := hopen0.restrictPreimage E
  have hclosed : IsClosedMap f := hclosed0.restrictPreimage E
  let y : E := ⟨0, hzero⟩
  let z0 : K := ⟨0, by simpa [K, zero_pow (by omega : m ≠ 0)] using hzero⟩
  have hfiber : f ⁻¹' {y} ⊆ ({z0} : Set K) := by
    intro z hz
    have hval : (z : ℂ) ^ m = 0 := congrArg Subtype.val hz
    have hz0 : (z : ℂ) = 0 := by
      by_contra hn
      exact (pow_ne_zero m hn) hval
    have : z = z0 := Subtype.ext hz0
    simpa only [mem_singleton_iff] using this
  letI : PreconnectedSpace K :=
    preconnectedSpace_of_open_closed_fiber_bridge f hopen hclosed y
      ({z0} : Set K) isPreconnected_singleton hfiber
  have hK : IsPreconnected K :=
    isPreconnected_iff_preconnectedSpace.2 inferInstance
  simpa [K, Set.preimage] using hK

/-- The actual omitted set of every odd-star deformation is a connected
plane continuum. This supplies the geometric hypothesis of the factor
constant problem for the explicit perturbations. -/
theorem oddStarPerturbation_omitted_connected
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    IsConnected (oddStarPerturbationOmitted m t) := by
  rw [oddStarPerturbation_omitted_eq_power_preimage m hm t ht]
  have hpre := power_preimage_isPreconnected_of_zero_mem m (by omega)
    (oddStarSeedOmitted t)
    (oddStarSeed_omitted_connected t ht).isPreconnected
    (oddStarSeed_zero_mem_omitted t ht)
  refine ⟨?_, hpre⟩
  exact ⟨0, by
    change (0 : ℂ) ^ m ∈ oddStarSeedOmitted t
    simpa [zero_pow (by omega : m ≠ 0)] using
      oddStarSeed_zero_mem_omitted t ht⟩

end SpringerLean

#print axioms SpringerLean.power_preimage_isPreconnected_of_zero_mem
#print axioms SpringerLean.oddStarPerturbation_omitted_connected
