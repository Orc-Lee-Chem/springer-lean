import SpringerLean

namespace SpringerLean.PaperStatementsAudit
open Set Real MeasureTheory Polynomial Filter Metric
open scoped Topology

theorem theorem_1_1_large_751_singleRamp
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) :
    ‖exteriorInverseCoeff F (2*k-1)‖ ≤ (catalan (k-1) : ℝ) ∧
      (‖exteriorInverseCoeff F (2*k-1)‖ = (catalan (k-1) : ℝ) ↔
        ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :=
  AnalyticRevision.exteriorInverseCoeff_large_catalan_and_eq_iff_slit_singleRamp F hc k hk

theorem lemma_9_2_connected_lemniscate_exterior_identity
    (Q : Polynomial ℂ) (hQ : Q.Monic) (hn : 0 < Q.natDegree) (hsum : Q.roots.sum = 0)
    (hconn : IsConnected {z : ℂ | ‖Q.eval z‖ ≤ 1}) :
    ∃ F : ℂ → ℂ, CenteredExteriorUnivalent F ∧
      (∀ w ∈ exteriorDisk, Q.eval (F w) = w ^ Q.natDegree) :=
  connectedLemniscateExteriorExistence_proved Q hQ hn hsum hconn

theorem proposition_9_2_strict_derivative_zero_moment
    (P : Polynomial ℂ) (hP : 2 ≤ P.natDegree) (t : ℝ) (ht : 0 < t)
    (hK : IsConnected {w : ℂ | ‖P.eval w‖ ≤ t})
    (j : ℕ) (hj : j < P.natDegree) (p : ℝ) (hp4 : 4 ≤ p) (hp8 : p ≤ 8) :
    ((((Polynomial.derivative^[j]) P).roots.map
      (fun w : ℂ => ‖(w - polynomialZeroCentroid P) /
        (polynomialLemniscateRadius P t : ℂ)‖ ^ p)).sum) /
      ((P.natDegree - j : ℕ) : ℝ) < slitRadialMomentConstant p :=
  originalPolynomial_derivative_root_power_mean_strict P hP t ht hK j hj p hp4 hp8

theorem proposition_9_2_exact_supremum_and_nonattainment
    (j : ℕ) (p : ℝ) (hp4 : 4 ≤ p) (hp8 : p ≤ 8) :
    sSup (connectedPolynomialDerivativeMoments j p) = slitRadialMomentConstant p ∧
      slitRadialMomentConstant p ∉ connectedPolynomialDerivativeMoments j p :=
  connectedPolynomialDerivativeMoments_csSup_and_not_attained j p hp4 hp8

theorem lemma_10_1_actual_radial_probability_is_equilibrium
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) :
    IsProbabilityMeasure (actualExteriorBoundaryProbability F) ∧
    exteriorOmitted F ∈ ae (actualExteriorBoundaryProbability F) ∧
    twiceShiftedLogEnergy (actualExteriorBoundaryProbability F)
      (actualExteriorBoundaryProbability F) = ENNReal.ofReal (2 * Real.log 5) ∧
    ∀ (ν : Measure ℂ) [IsProbabilityMeasure ν], exteriorOmitted F ∈ ae ν →
      ENNReal.ofReal (2 * Real.log 5) ≤ twiceShiftedLogEnergy ν ν ∧
      (twiceShiftedLogEnergy ν ν = ENNReal.ofReal (2 * Real.log 5) ↔
        ν = actualExteriorBoundaryProbability F) := by
  have hprob : IsProbabilityMeasure (actualExteriorBoundaryProbability F) :=
    ⟨actualExteriorBoundaryProbability_univ F hF⟩
  have hmem := actualExteriorBoundaryProbability_ae_mem_omitted F hF
    (exteriorOmitted_isCompact F hF).isClosed
  have hself := (actualExteriorBoundaryProbability_minimizes_log_energy
    F hF _ hmem).1
  refine ⟨hprob, hmem, hself, ?_⟩
  intro ν _ hν
  have hle := (actualExteriorBoundaryProbability_minimizes_log_energy F hF ν hν).2
  rw [hself] at hle
  exact ⟨hle, ⟨actualExteriorBoundaryProbability_unique_log_energy_minimizer F hF ν hν,
    fun h => by simpa only [h] using hself⟩⟩

theorem lemma_10_1_actual_factor_constant_formula
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (u v : ℂ) (hu : u ∈ exteriorOmitted F) (hv : v ∈ exteriorOmitted F) (huv : u ≠ v) :
    factorConstant (exteriorOmitted F) = Real.exp
      (∫ z, Real.log (continuumFarthestDistance (exteriorOmitted F) z)
        ∂actualExteriorBoundaryProbability F) :=
  factorConstant_eq_actual_farthest_exp F hF u v hu hv huv

theorem theorem_10_1_even_normalized_exterior
    (K : Set ℂ) (hK : IsCompact K) (hc : IsConnected K) (k : ℕ) (hk : 0 < k)
    (hrot : EvenGeneratorInvariant K k) (u v : ℂ) (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v)
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (hIm : F '' exteriorDisk = (continuumFill K)ᶜ) :
    let S := regularStarRaySet (2*k)
    factorConstant K ≤ factorConstant S ∧
      (1-(k:ℝ)^2*‖exteriorForwardCoeff F (2*k-1)‖^2)/(96*(k:ℝ)^2) ≤
        log (factorConstant S/factorConstant K) ∧
      (factorConstant K = factorConstant S ↔
        ∃ b : ℂ, ‖b‖ = 1 ∧ K = (fun z : ℂ => b*z) '' S) :=
  evenStar_filled_normalized_factorConstant K hK hc k hk hrot u v hu hv huv F hF hIm

theorem theorem_10_1_even_regular_star
    (K : Set ℂ) (hK : IsCompact K) (hc : IsConnected K) (k : ℕ) (hk : 0 < k)
    (c : ℂ) (hrot : ContinuumRotationInvariant K (2*k) c)
    (u v : ℂ) (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v) :
    let S := regularStarRaySet (2*k)
    ∃ (r : ℝ) (F : ℂ → ℂ), 0 < r ∧ CenteredExteriorUnivalent F ∧
      F '' exteriorDisk = (continuumScale (continuumFill (continuumTranslate K (-c))) (r:ℂ))ᶜ ∧
      factorConstant K ≤ factorConstant S ∧
      (1-(k:ℝ)^2*‖exteriorForwardCoeff F (2*k-1)‖^2)/(96*(k:ℝ)^2) ≤
        log (factorConstant S/factorConstant K) ∧
      (factorConstant K = factorConstant S ↔
        ∃ b d : ℂ, b ≠ 0 ∧ K = continuumTranslate (continuumScale S b) d) :=
  evenRegularStar_factorConstant_actual K hK hc k hk c
    (continuumTranslate_evenGeneratorInvariant K k c hrot) u v hu hv huv

theorem theorem_10_1_regularity_parity (m : ℕ) (hm : 2 ≤ m) :
    (∀ K : Set ℂ, IsCompact K → IsConnected K →
      (∃ u v : ℂ, u ∈ K ∧ v ∈ K ∧ u ≠ v) →
      ∀ c : ℂ, ContinuumRotationInvariant K m c →
        factorConstant K ≤ factorConstant (regularStarRaySet m)) ↔ Even m :=
  regularStar_universal_factorConstant_iff_even m hm

theorem theorem_10_1_odd_regular_star_counterexample
    (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m) :
    ∃ K : Set ℂ, IsCompact K ∧ IsConnected K ∧
      (∃ u v : ℂ, u ∈ K ∧ v ∈ K ∧ u ≠ v) ∧
      (∀ η z : ℂ, η ^ m = 1 → (η * z ∈ K ↔ z ∈ K)) ∧
      factorConstant (regularStarRaySet m) < factorConstant K :=
  odd_regularStar_factorConstant_counterexample m hm hodd

end SpringerLean.PaperStatementsAudit

#check @SpringerLean.PaperStatementsAudit.theorem_1_1_large_751_singleRamp
#print axioms SpringerLean.PaperStatementsAudit.theorem_1_1_large_751_singleRamp
#check @SpringerLean.PaperStatementsAudit.lemma_9_2_connected_lemniscate_exterior_identity
#print axioms SpringerLean.PaperStatementsAudit.lemma_9_2_connected_lemniscate_exterior_identity
#check @SpringerLean.PaperStatementsAudit.proposition_9_2_strict_derivative_zero_moment
#print axioms SpringerLean.PaperStatementsAudit.proposition_9_2_strict_derivative_zero_moment
#check @SpringerLean.PaperStatementsAudit.proposition_9_2_exact_supremum_and_nonattainment
#print axioms SpringerLean.PaperStatementsAudit.proposition_9_2_exact_supremum_and_nonattainment
#check @SpringerLean.PaperStatementsAudit.lemma_10_1_actual_radial_probability_is_equilibrium
#print axioms SpringerLean.PaperStatementsAudit.lemma_10_1_actual_radial_probability_is_equilibrium
#check @SpringerLean.PaperStatementsAudit.lemma_10_1_actual_factor_constant_formula
#print axioms SpringerLean.PaperStatementsAudit.lemma_10_1_actual_factor_constant_formula
#check @SpringerLean.PaperStatementsAudit.theorem_10_1_even_normalized_exterior
#print axioms SpringerLean.PaperStatementsAudit.theorem_10_1_even_normalized_exterior
#check @SpringerLean.PaperStatementsAudit.theorem_10_1_even_regular_star
#print axioms SpringerLean.PaperStatementsAudit.theorem_10_1_even_regular_star
#check @SpringerLean.PaperStatementsAudit.theorem_10_1_regularity_parity
#print axioms SpringerLean.PaperStatementsAudit.theorem_10_1_regularity_parity
#check @SpringerLean.PaperStatementsAudit.theorem_10_1_odd_regular_star_counterexample
#print axioms SpringerLean.PaperStatementsAudit.theorem_10_1_odd_regular_star_counterexample
#check @SpringerLean.PaperStatementsAudit.theorem_9_1_p2_actual_radial
#print axioms SpringerLean.PaperStatementsAudit.theorem_9_1_p2_actual_radial
#check @SpringerLean.PaperStatementsAudit.theorem_9_1_p4_actual_radial
#print axioms SpringerLean.PaperStatementsAudit.theorem_9_1_p4_actual_radial
#check @SpringerLean.PaperStatementsAudit.theorem_9_1_p6_actual_radial_strong
#print axioms SpringerLean.PaperStatementsAudit.theorem_9_1_p6_actual_radial_strong
#check @SpringerLean.PaperStatementsAudit.theorem_9_1_p8_actual_radial_strong
#print axioms SpringerLean.PaperStatementsAudit.theorem_9_1_p8_actual_radial_strong
#check @SpringerLean.PaperStatementsAudit.theorem_9_1_p4_to_p8_actual_radial
#print axioms SpringerLean.PaperStatementsAudit.theorem_9_1_p4_to_p8_actual_radial
