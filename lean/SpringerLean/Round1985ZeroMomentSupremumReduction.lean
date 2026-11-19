import SpringerLean.Round1984ComplexChebyshevWitness

open Polynomial Set

namespace SpringerLean

/-- The exact zero-moment values of centered monic complex polynomials
with connected unit lemniscates and derivative order below degree. -/
noncomputable def connectedLemniscateDerivativeZeroMoments
    (j : ℕ) (p : ℝ) : Set ℝ :=
  {v | ∃ Q : ℂ[X], Q.Monic ∧ j < Q.natDegree ∧
    Q.roots.sum = 0 ∧
    IsConnected {z : ℂ | ‖Q.eval z‖ ≤ 1} ∧
    v = ((((derivative^[j]) Q).roots.map
      (fun z : ℂ => ‖z‖ ^ p)).sum) /
        ((Q.natDegree - j : ℕ) : ℝ)}

theorem monicChebyshevCandidate_complex_natDegree
    (n : ℕ) :
    ((monicChebyshevCandidate n).map (algebraMap ℝ ℂ)).natDegree = n := by
  have hscale : monicChebyshevScale n ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
  have hreal : (monicChebyshevCandidate n).natDegree = n := by
    unfold monicChebyshevCandidate
    rw [natDegree_comp, natDegree_C_mul_X _ hscale,
      Chebyshev.natDegree_T, Int.natAbs_natCast]
    omega
  rw [natDegree_map (algebraMap ℝ ℂ), hreal]

/-- The complex Chebyshev witness belongs to the exact admissible
moment set and approaches the slit constant from below. -/
theorem connectedLemniscateDerivativeZeroMoments_near
    (j : ℕ) (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) :
    ∃ v ∈ connectedLemniscateDerivativeZeroMoments j p,
      slitRadialMomentConstant p - ε < v := by
  obtain ⟨n, hj, hmonic, hsum, hconn, hnear⟩ :=
    complexMonicChebyshevDerivative_sharpness_witness j p ε hp hε
  let Q : ℂ[X] := (monicChebyshevCandidate n).map (algebraMap ℝ ℂ)
  have hdeg : Q.natDegree = n :=
    monicChebyshevCandidate_complex_natDegree n
  let v : ℝ :=
    ((((derivative^[j]) Q).roots.map (fun z : ℂ => ‖z‖ ^ p)).sum) /
      ((Q.natDegree - j : ℕ) : ℝ)
  refine ⟨v, ?_, ?_⟩
  · exact ⟨Q, hmonic, by simpa [hdeg] using hj, hsum, hconn, rfl⟩
  · simpa [v, Q, hdeg] using hnear

/-- Once the unrestricted upper bound is supplied for the exact
admissible class, the already formalized complex Chebyshev witnesses
make the cross-degree supremum exactly `S(p)`. The upper hypothesis is
explicit; this is a reduction, not a final 9.2 theorem. -/
theorem connectedLemniscateDerivativeZeroMoments_csSup_of_upper
    (j : ℕ) (p : ℝ) (hp : 0 < p)
    (hupper : ∀ v ∈ connectedLemniscateDerivativeZeroMoments j p,
      v ≤ slitRadialMomentConstant p) :
    sSup (connectedLemniscateDerivativeZeroMoments j p) =
      slitRadialMomentConstant p := by
  let S : Set ℝ := connectedLemniscateDerivativeZeroMoments j p
  have hne : S.Nonempty := by
    obtain ⟨v, hv, _⟩ :=
      connectedLemniscateDerivativeZeroMoments_near j p 1 hp (by norm_num)
    exact ⟨v, hv⟩
  have hbdd : BddAbove S := ⟨slitRadialMomentConstant p, hupper⟩
  apply le_antisymm
  · exact csSup_le hne hupper
  · by_contra hnot
    have hlt : sSup S < slitRadialMomentConstant p := lt_of_not_ge hnot
    let ε : ℝ := (slitRadialMomentConstant p - sSup S) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨v, hv, hnear⟩ :=
      connectedLemniscateDerivativeZeroMoments_near j p ε hp hε
    have hvle : v ≤ sSup S := le_csSup hbdd hv
    dsimp [ε] at hnear
    linarith

end SpringerLean

#print axioms SpringerLean.connectedLemniscateDerivativeZeroMoments_near
#print axioms SpringerLean.connectedLemniscateDerivativeZeroMoments_csSup_of_upper
