import SpringerLean.Round1792SelectedOuterPhaseProjections

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 500000

def endpointPhaseY (k : ℕ) (P : ℂ) : ℝ :=
  (((2*k-2 : ℕ) : ℝ)*(2-‖P‖)*Real.log (2/(2-‖P‖)))/3

def endpointPhaseParameter (k : ℕ) (P : ℂ) : ℝ :=
  min (3/endpointPhaseY k P) (((2*k-2 : ℕ) : ℝ)/5)

/-- The paper's y and a are fixed from the actual localized endpoint;
all their admissibility conditions follow from the accepted data. -/
theorem endpointPhaseParameter_bounds
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ)
    (hd : 0 < 2-‖P‖)
    (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hlog : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖)*Real.log (2/(2-‖P‖)) < 3/2)
    (hwidth : exteriorFineEndpointWidth P <
      (1/3 : ℝ)*(2-‖P‖)*Real.log (2/(2-‖P‖))) :
    0 < endpointPhaseY k P ∧ endpointPhaseY k P < 1/2 ∧
      6 ≤ endpointPhaseParameter k P ∧
      endpointPhaseParameter k P ≤ ((2*k-2 : ℕ) : ℝ)/5 ∧
      endpointPhaseParameter k P*(((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P) ≤ 3 := by
  have hm : (1500 : ℝ) ≤ ((2*k-2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1500 ≤ 2*k-2)
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1501 ≤ 2*k-1)
  have hmn : ((2*k-2 : ℕ) : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2*k-2 ≤ 2*k-1)
  have hm0 : (0 : ℝ) < ((2*k-2 : ℕ) : ℝ) := by linarith
  have hd1 : 2-‖P‖ < 1 := by nlinarith [mul_le_mul_of_nonneg_right hn hd.le]
  have hL : 0 < Real.log (2/(2-‖P‖)) := by
    apply Real.log_pos
    apply (lt_div_iff₀ hd).mpr
    linarith
  have hY0 : 0 < endpointPhaseY k P := by unfold endpointPhaseY; positivity
  have hY1 : endpointPhaseY k P < 1/2 := by
    have hh := mul_le_mul_of_nonneg_right hmn
      (mul_nonneg hd.le hL.le)
    unfold endpointPhaseY
    nlinarith
  have hA6 : 6 ≤ endpointPhaseParameter k P := by
    unfold endpointPhaseParameter
    apply le_min
    · apply (le_div_iff₀ hY0).mpr
      linarith
    · linarith
  have hAupper : endpointPhaseParameter k P ≤ ((2*k-2 : ℕ) : ℝ)/5 := min_le_right _ _
  have hAY : endpointPhaseParameter k P*endpointPhaseY k P ≤ 3 := by
    calc
      _ ≤ (3/endpointPhaseY k P)*endpointPhaseY k P :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hY0.le
      _ = 3 := div_mul_cancel₀ _ hY0.ne'
  have hW : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P < endpointPhaseY k P := by
    have hh := mul_lt_mul_of_pos_left hwidth hm0
    unfold endpointPhaseY
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hW.le (show 0 ≤ endpointPhaseParameter k P by linarith)
  exact ⟨hY0,hY1,hA6,hAupper,hh.trans hAY⟩

end
end SpringerLean

#print axioms SpringerLean.endpointPhaseParameter_bounds
