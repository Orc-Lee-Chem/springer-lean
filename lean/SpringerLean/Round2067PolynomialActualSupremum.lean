import SpringerLean.Round2066ConnectedLemniscateExterior

open Polynomial Set Filter

namespace SpringerLean

/-- The original scale and centroid remain fixed for each polynomial
and its connected sublevel set, regardless of derivative order. -/
noncomputable def normalizedDerivativeZeroMoment
    (P : ℂ[X]) (t : ℝ) (j : ℕ) (p : ℝ) : ℝ :=
  ((((derivative^[j]) P).roots.map
    (fun w : ℂ => ‖(w - polynomialZeroCentroid P) /
      (polynomialLemniscateRadius P t : ℂ)‖ ^ p)).sum) /
    ((P.natDegree - j : ℕ) : ℝ)

/-- All admissible values for fixed derivative order and exponent,
over all original polynomials of degree at least two and all levels. -/
def connectedPolynomialDerivativeMoments (j : ℕ) (p : ℝ) : Set ℝ :=
  {v | ∃ (P : ℂ[X]) (t : ℝ), 2 ≤ P.natDegree ∧ j < P.natDegree ∧
    0 < t ∧ IsConnected {w : ℂ | ‖P.eval w‖ ≤ t} ∧
      v = normalizedDerivativeZeroMoment P t j p}

/-- The general strict zero-moment bound from the original lemniscate
hypotheses, for all derivative orders below the degree. -/
theorem originalPolynomial_derivative_root_power_mean_strict
    (P : ℂ[X]) (hP : 2 ≤ P.natDegree) (t : ℝ) (ht : 0 < t)
    (hK : IsConnected {w : ℂ | ‖P.eval w‖ ≤ t})
    (j : ℕ) (hj : j < P.natDegree) (p : ℝ) (hp4 : 4 ≤ p) (hp8 : p ≤ 8) :
    normalizedDerivativeZeroMoment P t j p < slitRadialMomentConstant p :=
  originalPolynomial_derivative_root_power_mean_strict_of_exterior
    connectedLemniscateExteriorExistence_proved P (by omega) t ht hK j hj p hp4 hp8

theorem connectedPolynomialDerivativeMoments_near
    (j : ℕ) (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) :
    ∃ v ∈ connectedPolynomialDerivativeMoments j p, slitRadialMomentConstant p - ε < v := by
  have hlim := monicChebyshevDerivativeRadialMoment_tendsto_slit_constant j p hp
  have hnear : ∀ᶠ n : ℕ in atTop,
      slitRadialMomentConstant p - ε < monicChebyshevDerivativeRadialMoment n j p :=
    hlim.eventually (eventually_gt_nhds (by linarith))
  obtain ⟨n,hn₂,hj,hnr⟩ := ((eventually_ge_atTop (2 : ℕ)).and
    ((eventually_gt_atTop j).and hnear)).exists
  have hn0 : 0 < n := by omega
  let P := (monicChebyshevCandidate n).map (algebraMap ℝ ℂ)
  have hdeg : P.natDegree = n := monicChebyshevCandidate_complex_natDegree n
  have hmonic : P.Monic := (monicChebyshevCandidate_monic n hn0).map (algebraMap ℝ ℂ)
  have hconn : IsConnected {z : ℂ | ‖P.eval z‖ ≤ 1} :=
    monicChebyshevCandidate_unit_lemniscate_connected n hn0
  have hsum : P.roots.sum = 0 := by
    have hroots : (monicChebyshevCandidate n).roots.map (algebraMap ℝ ℂ) = P.roots :=
      roots_map_of_injective_of_card_eq_natDegree
        (FaithfulSMul.algebraMap_injective ℝ ℂ)
        (by simpa using monicChebyshev_derivative_roots_card_eq_natDegree n 0)
    rw [← hroots, ← map_multiset_sum, monicChebyshevCandidate_roots_sum_zero]
    simp
  have hscale : polynomialLemniscateRadius P 1 = 1 := by
    simp [polynomialLemniscateRadius, hmonic.leadingCoeff]
  have hcenter : polynomialZeroCentroid P = 0 := by simp [polynomialZeroCentroid, hsum]
  have hmoment : normalizedDerivativeZeroMoment P 1 j p =
      monicChebyshevDerivativeRadialMoment n j p := by
    unfold normalizedDerivativeZeroMoment
    rw [hscale, hcenter, hdeg]
    simp only [sub_zero, Complex.ofReal_one, div_one]
    exact monicChebyshevDerivativeRadialMoment_complex_eq n j hj p
  exact ⟨_, ⟨P,1,hdeg.symm ▸ hn₂,hdeg.symm ▸ hj,by norm_num,hconn,rfl⟩, hmoment.symm ▸ hnr⟩

/-- The exact supremum of actual admissible normalized derivative
moments. No polynomial and positive level attain this value. -/
theorem connectedPolynomialDerivativeMoments_csSup_and_not_attained
    (j : ℕ) (p : ℝ) (hp4 : 4 ≤ p) (hp8 : p ≤ 8) :
    sSup (connectedPolynomialDerivativeMoments j p) = slitRadialMomentConstant p ∧
      slitRadialMomentConstant p ∉ connectedPolynomialDerivativeMoments j p := by
  have hp : 0 < p := by linarith
  let T := connectedPolynomialDerivativeMoments j p
  have hupper : ∀ v ∈ T, v < slitRadialMomentConstant p := by
    rintro _ ⟨P,t,hP,hj,ht,hK,rfl⟩
    exact originalPolynomial_derivative_root_power_mean_strict P hP t ht hK j hj p hp4 hp8
  have hb : BddAbove T := ⟨_, fun _ h => (hupper _ h).le⟩
  have hne : T.Nonempty := by
    obtain ⟨v,hv,_⟩ := connectedPolynomialDerivativeMoments_near j p 1 hp (by norm_num)
    exact ⟨v,hv⟩
  refine ⟨le_antisymm (csSup_le hne (fun v hv => (hupper v hv).le)) ?_, ?_⟩
  · by_contra! hlt
    let ε := (slitRadialMomentConstant p - sSup T)/2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨v,hv,hvlt⟩ := connectedPolynomialDerivativeMoments_near j p ε hp hε
    have hvle := le_csSup hb hv
    dsimp [ε] at hvlt
    linarith
  · exact fun h => (lt_irrefl _) (hupper _ h)

end SpringerLean
