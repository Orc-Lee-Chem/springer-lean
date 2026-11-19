import SpringerLean.Round1983ChebyshevComplexMoment

open Polynomial

namespace SpringerLean

/-- The R1875 near-sharp witness expressed entirely in the complex
polynomial class used by Proposition 9.2, with the derivative zeros
counted by their complex multiplicities. -/
theorem complexMonicChebyshevDerivative_sharpness_witness
    (j : ℕ) (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) :
    ∃ n : ℕ, j < n ∧
      (((monicChebyshevCandidate n).map (algebraMap ℝ ℂ)).Monic) ∧
      (((monicChebyshevCandidate n).map (algebraMap ℝ ℂ)).roots.sum = 0) ∧
      IsConnected {z : ℂ |
        ‖((monicChebyshevCandidate n).map (algebraMap ℝ ℂ)).eval z‖ ≤ 1} ∧
      slitRadialMomentConstant p - ε <
        (((((derivative^[j])
          ((monicChebyshevCandidate n).map (algebraMap ℝ ℂ))).roots).map
            (fun z : ℂ => ‖z‖ ^ p)).sum) /
              ((n - j : ℕ) : ℝ) := by
  obtain ⟨n, hj, hmonic, hsum, hconn, hnear⟩ :=
    monicChebyshevDerivative_sharpness_witness j p ε hp hε
  let P : ℝ[X] := monicChebyshevCandidate n
  have hroots : P.roots.map (algebraMap ℝ ℂ) =
      (P.map (algebraMap ℝ ℂ)).roots :=
    roots_map_of_injective_of_card_eq_natDegree
      (FaithfulSMul.algebraMap_injective ℝ ℂ)
      (by simpa [P] using monicChebyshev_derivative_roots_card_eq_natDegree n 0)
  have hsumC : (P.map (algebraMap ℝ ℂ)).roots.sum = 0 := by
    rw [← hroots, ← map_multiset_sum]
    simp [P, hsum]
  have hmoment := monicChebyshevDerivativeRadialMoment_complex_eq n j hj p
  refine ⟨n, hj, hmonic.map (algebraMap ℝ ℂ), hsumC, hconn, ?_⟩
  rw [hmoment]
  exact hnear

end SpringerLean

#print axioms SpringerLean.complexMonicChebyshevDerivative_sharpness_witness
