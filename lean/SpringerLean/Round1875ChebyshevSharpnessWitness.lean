import SpringerLean.Round1874ChebyshevLemniscate
import SpringerLean.Round1865ArcsineGammaMoment
import SpringerLean.Round790ChebyshevRootSymmetry

open Filter Polynomial

namespace SpringerLean

/-- For each positive real exponent and fixed derivative order, actual
admissible monic Chebyshev polynomials approach the sharp constant from
below.  This packages the connectedness, centering, multiplicity-aware
derivative moment, and exact Gamma limit into one witness statement. -/
theorem monicChebyshevDerivative_sharpness_witness
    (j : ℕ) (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) :
    ∃ n : ℕ, j < n ∧
      (monicChebyshevCandidate n).Monic ∧
      (monicChebyshevCandidate n).roots.sum = 0 ∧
      IsConnected {z : ℂ |
        ‖((monicChebyshevCandidate n).map (algebraMap ℝ ℂ)).eval z‖ ≤ 1} ∧
      slitRadialMomentConstant p - ε <
        monicChebyshevDerivativeRadialMoment n j p := by
  have hlim := monicChebyshevDerivativeRadialMoment_tendsto_slit_constant j p hp
  have hnear : ∀ᶠ n : ℕ in atTop,
      slitRadialMomentConstant p - ε <
        monicChebyshevDerivativeRadialMoment n j p :=
    hlim.eventually (eventually_gt_nhds (by linarith))
  obtain ⟨n, hn, hbound⟩ := (eventually_gt_atTop j |>.and hnear).exists
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le j) hn
  exact ⟨n, hn, monicChebyshevCandidate_monic n hn0,
    monicChebyshevCandidate_roots_sum_zero n,
    monicChebyshevCandidate_unit_lemniscate_connected n hn0, hbound⟩

end SpringerLean

#check @SpringerLean.monicChebyshevDerivative_sharpness_witness
#print axioms SpringerLean.monicChebyshevDerivative_sharpness_witness
