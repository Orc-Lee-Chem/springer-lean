import SpringerLean.Round1875ChebyshevSharpnessWitness

open Polynomial

namespace SpringerLean

/-- Every real derivative root of the scaled monic Chebyshev polynomial
is accounted for, including multiplicity. -/
theorem monicChebyshev_derivative_roots_card_eq_natDegree
    (n j : ℕ) :
    (((derivative^[j]) (monicChebyshevCandidate n)).roots).card =
      ((derivative^[j]) (monicChebyshevCandidate n)).natDegree := by
  let P : ℝ[X] := (derivative^[j]) (monicChebyshevCandidate n)
  have hcard : P.roots.card = n - j := by
    rw [monicChebyshevCandidate_derivative_roots, Multiset.card_map]
    exact chebyshev_iterated_derivative_real_roots n j
  have hdegree : P.natDegree ≤ n - j := by
    dsimp [P]
    have hscale : monicChebyshevScale n ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have hcandidate : (monicChebyshevCandidate n).natDegree = n := by
      unfold monicChebyshevCandidate
      rw [natDegree_comp, natDegree_C_mul_X _ hscale,
        Chebyshev.natDegree_T, Int.natAbs_natCast]
      omega
    calc
      _ ≤ (monicChebyshevCandidate n).natDegree - j :=
        natDegree_iterate_derivative _ _
      _ = n - j := by rw [hcandidate]
  have hrootle : P.roots.card ≤ P.natDegree := P.card_roots'
  change P.roots.card = P.natDegree
  omega

/-- Complexification preserves the exact normalized derivative-zero
moment of the real monic Chebyshev witness. -/
theorem monicChebyshevDerivativeRadialMoment_complex_eq
    (n j : ℕ) (hj : j < n) (p : ℝ) :
    (((((derivative^[j])
      ((monicChebyshevCandidate n).map (algebraMap ℝ ℂ))).roots).map
        (fun z : ℂ => ‖z‖ ^ p)).sum) /
          ((n - j : ℕ) : ℝ) =
      monicChebyshevDerivativeRadialMoment n j p := by
  let P : ℝ[X] := (derivative^[j]) (monicChebyshevCandidate n)
  have hroots : P.roots.map (algebraMap ℝ ℂ) =
      (P.map (algebraMap ℝ ℂ)).roots :=
    roots_map_of_injective_of_card_eq_natDegree
      (FaithfulSMul.algebraMap_injective ℝ ℂ)
      (monicChebyshev_derivative_roots_card_eq_natDegree n j)
  rw [iterate_derivative_map]
  rw [← hroots]
  unfold monicChebyshevDerivativeRadialMoment
  have hnorm (x : ℝ) : ‖(algebraMap ℝ ℂ) x‖ = |x| := by
    simp
  simp only [Multiset.map_map, Function.comp_def, hnorm]
  have hden : ((n - j : ℕ) : ℝ) = (n : ℝ) - j := by
    exact Nat.cast_sub hj.le
  rw [hden]

end SpringerLean

#print axioms SpringerLean.monicChebyshev_derivative_roots_card_eq_natDegree
#print axioms SpringerLean.monicChebyshevDerivativeRadialMoment_complex_eq
