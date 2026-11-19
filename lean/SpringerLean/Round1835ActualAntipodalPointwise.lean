import SpringerLean.Round1834TinyOuterPhaseCone

open scoped ComplexConjugate

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 1400000

theorem phase_square_antipode (beta v : ℂ) (k : ℕ)
    (hphase : (beta*v^k)^2=1) : (beta*(-v)^k)^2=1 := by
  have hneg : ((-v)^k)^2=(v^k)^2 := by
    calc
      _ = ((-v)^2)^k := pow_right_comm _ _ _
      _ = (v^2)^k := by rw [neg_sq]
      _ = _ := (pow_right_comm _ _ _).symm
  rw [mul_pow,hneg,←mul_pow]
  exact hphase

def antipodalPhaseTest (k : ℕ) (v w : ℂ) : ℝ :=
  (max ((conj v*w).re) 0)^(2*k-2)/(2 : ℝ)^(2*k-2)+
    (max ((conj (-v)*w).re) 0)^(2*k-2)/(2 : ℝ)^(2*k-2)

theorem antipodalPhaseTest_nonneg (k : ℕ) (v w : ℂ) : 0 ≤ antipodalPhaseTest k v w := by
  unfold antipodalPhaseTest
  positivity

/-- A variable central allowance, valid on the actual full source
disk; the same first endpoint supplies both antipodal phase rays. -/
theorem actualSignedPhaseDensity_antipodal_global
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ)
    (ends : ActualCandidatePhaseEndpoints F k beta)
    (z : ℂ) (hz : ‖z‖ < 1) :
    let E := (2-‖ends.P₁‖)*Real.log (2/(2-‖ends.P₁‖))
    actualSignedPhaseDensity F k beta z ≤
      antipodalPhaseTest k ends.v₁ (actualHarmonic F z)+
        (3*(k : ℝ)*Real.sqrt E)^(2*k-2) := by
  let E := (2-‖ends.P₁‖)*Real.log (2/(2-‖ends.P₁‖))
  let ξ := ends.P₁/(‖ends.P₁‖ : ℂ)
  let w := actualHarmonic F z
  have hL := (endpointPhaseParameter_scalar_relations k hk ends.P₁ ends.deficit_pos₁ ends.scaled_deficit₁).1
  have hE : 0 < E := by
    have hL0 : 0 < Real.log (2/(2-‖ends.P₁‖)) := by linarith
    exact mul_pos ends.deficit_pos₁ hL0
  have hP := (ActualCandidatePhaseEndpoints.radius_pos F k hk beta ends).1
  have hξ : ‖ξ‖=1 := by
    dsimp [ξ]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hP,div_self hP.ne']
  have htrans := exteriorOmitted_actualEndpoint_transverse_le_deficit F hc k hk ends.P₁ ends.mem₁
    ends.deficit_pos₁ ends.scaled_deficit₁ ends.log_localization₁ ends.fine_width₁ w
    (actualHarmonic_mem_convexHull_omitted F hc hz)
  change |(conj ξ*w).im| ≤ (5/2 : ℝ)*Real.sqrt E at htrans
  have htest := antipodalPhaseTest_nonneg k ends.v₁ w
  change actualSignedPhaseDensity F k beta z ≤ antipodalPhaseTest k ends.v₁ w+(3*(k : ℝ)*Real.sqrt E)^(2*k-2)
  by_cases houter : 6*(k : ℝ)*Real.sqrt E < ‖w‖
  · have hr0 : 0 < ‖w‖ := (show 0 < 6*(k : ℝ)*Real.sqrt E by positivity).trans houter
    have hpoint : actualSignedPhaseDensity F k beta z ≤ antipodalPhaseTest k ends.v₁ w := by
      by_cases hforward : 0 ≤ (conj ξ*w).re
      · obtain ⟨θ,hw,hθ,hproj⟩ := unit_perturbed_axis_tiny_outer_cone k hk hE ξ ends.v₁ w hξ
          ends.unit₁ ends.θ₁ ends.ray₁ ends.angle₁ hforward htrans houter
        have hh := actualSignedPhaseDensity_le_projected_of_aligned_polar F beta ends.v₁ z ends.unit₁ k hk
          ends.phase₁ hr0 hw hθ hproj.le
        unfold antipodalPhaseTest
        linarith [show 0 ≤ (max ((conj (-ends.v₁)*w).re) 0)^(2*k-2)/(2 : ℝ)^(2*k-2) by positivity]
      · have hforward' : 0 ≤ (conj (-ξ)*w).re := by
          simp only [map_neg,neg_mul,Complex.neg_re]
          linarith
        have htrans' : |(conj (-ξ)*w).im| ≤ (5/2 : ℝ)*Real.sqrt E := by
          simpa only [map_neg,neg_mul,Complex.neg_im,abs_neg] using htrans
        have hray : -ends.v₁=(-ξ)*Complex.exp ((ends.θ₁ : ℂ)*Complex.I) := by
          rw [ends.ray₁]
          ring
        obtain ⟨θ,hw,hθ,hproj⟩ := unit_perturbed_axis_tiny_outer_cone k hk hE (-ξ) (-ends.v₁) w
          (by simpa only [norm_neg] using hξ) (by simpa only [norm_neg] using ends.unit₁)
          ends.θ₁ hray ends.angle₁ hforward' htrans' houter
        have hh := actualSignedPhaseDensity_le_projected_of_aligned_polar F beta (-ends.v₁) z
          (by simpa only [norm_neg] using ends.unit₁) k hk
          (phase_square_antipode beta ends.v₁ k ends.phase₁) hr0 hw hθ hproj.le
        unfold antipodalPhaseTest
        linarith [show 0 ≤ (max ((conj ends.v₁*w).re) 0)^(2*k-2)/(2 : ℝ)^(2*k-2) by positivity]
    exact hpoint.trans (le_add_of_nonneg_right (by positivity))
  · have hsmall : ‖w‖/2 ≤ 3*(k : ℝ)*Real.sqrt E := by linarith
    have hpower := pow_le_pow_left₀ (by positivity : 0 ≤ ‖w‖/2) hsmall (2*k-2)
    rw [div_pow] at hpower
    have hpot : 0 ≤ actualHarmonicPhasePotentialDensity F k beta z := by
      unfold actualHarmonicPhasePotentialDensity
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hraw : ‖w‖^(2*k-2)-(8/25 : ℝ)*actualHarmonicPhasePotentialDensity F k beta z ≤ ‖w‖^(2*k-2) := by nlinarith
    have hsigned := div_le_div_of_nonneg_right hraw (by positivity : 0 ≤ (2 : ℝ)^(2*k-2))
    change actualSignedPhaseDensity F k beta z ≤ _ at hsigned
    linarith

end
end SpringerLean

#print axioms SpringerLean.actualSignedPhaseDensity_antipodal_global
