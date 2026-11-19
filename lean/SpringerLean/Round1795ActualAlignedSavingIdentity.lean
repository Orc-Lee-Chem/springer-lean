import SpringerLean.Round1794ActualBothAlignedIntegral

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 600000

def alignedPhaseReferenceCost (k : ℕ) (a : ℝ) : ℝ :=
  Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1,
    twoPowerPhaseTest (2*(1-a/((2*k-2 : ℕ) : ℝ))) (2*k-12) (2*z.re)/(2 : ℝ)^(2*k-2))

/-- Exact normalization bridge: the actual full-disk two-power saving
is m*sqrt(m) times reference cost minus actual cost. -/
theorem alignedPhaseTest_saving_identity
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (a : ℝ) (v : ℂ) (hv : ‖v‖=1) :
    (((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ))*
      (alignedPhaseReferenceCost k a-
        Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, alignedPhaseTest k a v (actualHarmonic F z))) =
      actualTwoPowerSaving F (2*k-12) (2*(1-a/((2*k-2 : ℕ) : ℝ))) v := by
  let g := twoPowerPhaseTest (2*(1-a/((2*k-2 : ℕ) : ℝ))) (2*k-12)
  have hg : Continuous g := by
    change Continuous (fun x : ℝ => max ((max x 0)^(2*k-12+10))
      ((2*(1-a/((2*k-2 : ℕ) : ℝ)))^8*(max x 0)^(2*k-12+2)))
    fun_prop
  have hga := actualHarmonic_projection_test_integrableOn F hc v hv g hg
  have hgm := comparisonDisk_test_integrableOn g hg
  have hi : 2*k-12+10=2*k-2 := by omega
  unfold alignedPhaseReferenceCost alignedPhaseTest actualTwoPowerSaving
  rw [hi, integral_sub hgm hga, integral_div, integral_div]
  ring

theorem ActualCandidatePhaseEndpoints.aligned_integral_savings
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ)
    (ends : ActualCandidatePhaseEndpoints F k beta)
    (a₁ a₂ : ℝ)
    (ha₁ : a₁ ≤ ((2*k-2 : ℕ) : ℝ)/5)
    (ha₂ : a₂ ≤ ((2*k-2 : ℕ) : ℝ)/5) :
    ((((2*k-2 : ℕ) : ℝ)*(2-‖ends.P₁‖))^3/32 <
      (((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ))*
        (alignedPhaseReferenceCost k a₁-
          Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, alignedPhaseTest k a₁ ends.v₁ (actualHarmonic F z)))) ∧
    ((((2*k-2 : ℕ) : ℝ)*(2-‖ends.P₂‖))^3/32 <
      (((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ))*
        (alignedPhaseReferenceCost k a₂-
          Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, alignedPhaseTest k a₂ ends.v₂ (actualHarmonic F z)))) := by
  have hm : (0 : ℝ) < ((2*k-2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 2*k-2)
  have hR {a : ℝ} (ha : a ≤ ((2*k-2 : ℕ) : ℝ)/5) :
      0 ≤ 2*(1-a/((2*k-2 : ℕ) : ℝ)) := by
    have hh : a/((2*k-2 : ℕ) : ℝ) ≤ 1 := (div_le_one hm).mpr (by linarith)
    linarith
  have h₁ := ends.saving₁ _ (hR ha₁)
  have h₂ := ends.saving₂ _ (hR ha₂)
  rw [←alignedPhaseTest_saving_identity F hc k hk a₁ ends.v₁ ends.unit₁] at h₁
  rw [←alignedPhaseTest_saving_identity F hc k hk a₂ ends.v₂ ends.unit₂] at h₂
  exact ⟨h₁,h₂⟩

end
end SpringerLean

#print axioms SpringerLean.alignedPhaseTest_saving_identity
#print axioms SpringerLean.ActualCandidatePhaseEndpoints.aligned_integral_savings
