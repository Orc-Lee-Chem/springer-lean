import SpringerLean.Round1771NearbyPhaseRay

open scoped ComplexConjugate

namespace SpringerLean

/-- A single actual endpoint pair, with its own nearby phase rays.
The record keeps the geometric hypotheses needed by BOTH phase
branches, and the actual two-power gains in one normalization. -/
structure ActualCandidatePhaseEndpoints (F : ℂ → ℂ) (k : ℕ) (beta : ℂ) where
  P₁ : ℂ
  P₂ : ℂ
  v₁ : ℂ
  v₂ : ℂ
  θ₁ : ℝ
  θ₂ : ℝ
  mem₁ : P₁ ∈ exteriorOmitted F
  mem₂ : P₂ ∈ exteriorOmitted F
  deficit_pos₁ : 0 < 2-‖P₁‖
  deficit_pos₂ : 0 < 2-‖P₂‖
  scaled_deficit₁ : ((2*k-1 : ℕ) : ℝ)*(2-‖P₁‖) < 3/20
  scaled_deficit₂ : ((2*k-1 : ℕ) : ℝ)*(2-‖P₂‖) < 3/20
  log_localization₁ : ((2*k-1 : ℕ) : ℝ)*(2-‖P₁‖)*Real.log (2/(2-‖P₁‖)) < 3/2
  log_localization₂ : ((2*k-1 : ℕ) : ℝ)*(2-‖P₂‖)*Real.log (2/(2-‖P₂‖)) < 3/2
  fine_width₁ : exteriorFineEndpointWidth P₁ < (1/3 : ℝ)*(2-‖P₁‖)*Real.log (2/(2-‖P₁‖))
  fine_width₂ : exteriorFineEndpointWidth P₂ < (1/3 : ℝ)*(2-‖P₂‖)*Real.log (2/(2-‖P₂‖))
  scaled_width₁ : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P₁ < 1/2
  scaled_width₂ : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P₂ < 1/2
  first_max : ∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖
  opposite : (conj (P₁/(‖P₁‖ : ℂ))*P₂).re ≤ 0
  second_max : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
    (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖
  unit₁ : ‖v₁‖=1
  unit₂ : ‖v₂‖=1
  ray₁ : v₁=(P₁/(‖P₁‖ : ℂ))*Complex.exp ((θ₁ : ℂ)*Complex.I)
  ray₂ : v₂=(P₂/(‖P₂‖ : ℂ))*Complex.exp ((θ₂ : ℂ)*Complex.I)
  angle₁ : |θ₁| ≤ Real.pi/(2*(k : ℝ))
  angle₂ : |θ₂| ≤ Real.pi/(2*(k : ℝ))
  phase₁ : (beta*v₁^k)^2=1
  phase₂ : (beta*v₂^k)^2=1
  saving₁ : ∀ R : ℝ, 0 ≤ R →
    ((((2*k-2 : ℕ) : ℝ)*(2-‖P₁‖))^3/32 < actualTwoPowerSaving F (2*k-12) R v₁)
  saving₂ : ∀ R : ℝ, 0 ≤ R →
    ((((2*k-2 : ℕ) : ℝ)*(2-‖P₂‖))^3/32 < actualTwoPowerSaving F (2*k-12) R v₂)

/-- Candidate localization, tilted caps, the two-power convex test,
and the actual coefficient phase can now use one consistent pair. -/
theorem exteriorInverseCoeff_candidate_phase_endpoints_nonempty
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk)
    (beta : ℂ) (hbeta : ‖beta‖=1) :
    Nonempty (ActualCandidatePhaseEndpoints F k beta) := by
  obtain ⟨P₁, P₂, hP₁, hP₂, hd₁, hd₂, ht₁, ht₂, hlog₁, hlog₂,
    hW₁, hW₂, hmW₁, hmW₂, hmax₁, hneg, hmax₂, hsave₁, hsave₂⟩ :=
    exteriorInverseCoeff_candidate_selected_two_tilted_twoPower_savings F hc k hk hB hns
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1501 ≤ 2*k-1)
  have hR₁ : 0 < ‖P₁‖ := by nlinarith [mul_le_mul_of_nonneg_right hn hd₁.le]
  have hR₂ : 0 < ‖P₂‖ := by nlinarith [mul_le_mul_of_nonneg_right hn hd₂.le]
  have haxis {P : ℂ} (hP : 0 < ‖P‖) : ‖P/(‖P‖ : ℂ)‖=1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hP, div_self hP.ne']
  obtain ⟨v₁, θ₁, hv₁, hray₁, ha₁, _, hp₁⟩ :=
    exists_nearby_unit_phase_ray_large beta (P₁/(‖P₁‖ : ℂ)) hbeta (haxis hR₁) hk
  obtain ⟨v₂, θ₂, hv₂, hray₂, ha₂, hclose₂, hp₂⟩ :=
    exists_nearby_unit_phase_ray_large beta (P₂/(‖P₂‖ : ℂ)) hbeta (haxis hR₂) hk
  exact ⟨⟨P₁, P₂, v₁, v₂, θ₁, θ₂, hP₁, hP₂, hd₁, hd₂,
    ht₁, ht₂, hlog₁, hlog₂, hW₁, hW₂, hmW₁, hmW₂, hmax₁, hneg, hmax₂,
    hv₁, hv₂, hray₁, hray₂, ha₁, ha₂, hp₁, hp₂,
    fun R hR => hsave₁ R hR v₁ hv₁,
    fun R hR => hsave₂ R hR v₂ hv₂ hclose₂⟩⟩

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_phase_endpoints_nonempty
