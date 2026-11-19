import SpringerLean.Round1830CandidateHasTinyEnd

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 900000

/-- The globally maximal first endpoint supplies the same cubic
positive-power gain in every unit direction, including antipodes. -/
theorem ActualCandidatePhaseEndpoints.first_all_direction_gains
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ)
    (ends : ActualCandidatePhaseEndpoints F k beta) :
    ∀ v : ℂ, ‖v‖=1 →
      ((((2*k-2 : ℕ) : ℝ)*(2-‖ends.P₁‖))^3/30 <
        actualDirectionalPowerSaving F (2*k-2) v) := by
  obtain ⟨hP₁,_⟩ := ActualCandidatePhaseEndpoints.radius_pos F k hk beta ends
  have hmn : ((2*k-2 : ℕ) : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2*k-2 ≤ 2*k-1)
  have hD : ((2*k-2 : ℕ) : ℝ)*(2-‖ends.P₁‖) ≤ 3/20 :=
    (mul_le_mul_of_nonneg_right hmn ends.deficit_pos₁.le).trans ends.scaled_deficit₁.le
  intro v hv
  apply actualHarmonic_positivePower_unitDisk_cubic_gain_of_radius F hc v hv ‖ends.P₁‖ hP₁
    (by linarith [ends.deficit_pos₁]) (by omega : 1500 ≤ 2*k-2) hD
  intro w hw
  calc
    (conj v*w).re ≤ ‖conj v*w‖ := Complex.re_le_norm _
    _ = ‖w‖ := by rw [norm_mul,Complex.norm_conj,hv,one_mul]
    _ ≤ ‖ends.P₁‖ := ends.first_max w hw

/-- The remaining tiny endpoint can always be the already selected
first endpoint; its actual global maximality is retained. -/
theorem exteriorInverseCoeff_candidate_first_endpoint_tiny
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ beta : ℂ, ‖beta‖=1 ∧ ∃ ends : ActualCandidatePhaseEndpoints F k beta,
      let m := ((2*k-2 : ℕ) : ℝ)
      m*(2-‖ends.P₁‖) < (3/100 : ℝ)/(m*Real.log (100*m)) ∧
      ∀ v : ℂ, ‖v‖=1 →
        (m*(2-‖ends.P₁‖))^3/30 < actualDirectionalPowerSaving F (2*k-2) v := by
  obtain ⟨beta,hbeta,ends,htiny⟩ := exteriorInverseCoeff_candidate_has_tiny_endpoint F hc k hk hB hns
  refine ⟨beta,hbeta,ends,?_,ActualCandidatePhaseEndpoints.first_all_direction_gains F hc k hk beta ends⟩
  have hR := ends.first_max ends.P₂ (subset_convexHull ℝ (exteriorOmitted F) ends.mem₂)
  have hm : 0 ≤ ((2*k-2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hD : ((2*k-2 : ℕ) : ℝ)*(2-‖ends.P₁‖) ≤ ((2*k-2 : ℕ) : ℝ)*(2-‖ends.P₂‖) :=
    mul_le_mul_of_nonneg_left (by linarith) hm
  dsimp only at htiny ⊢
  exact htiny.elim id (fun hh => hD.trans_lt hh)

end SpringerLean

#print axioms SpringerLean.ActualCandidatePhaseEndpoints.first_all_direction_gains
#print axioms SpringerLean.exteriorInverseCoeff_candidate_first_endpoint_tiny
