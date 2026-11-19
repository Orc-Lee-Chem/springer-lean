import SpringerLean.Round12Compact

open Filter
open scoped Topology

namespace SpringerLean
set_option Elab.async false

/-- Closed-graph limit of the genuine unscaled omitted collars. Initial
sequence terms need not be positive; convergence to one supplies every
fixed positive comparison scale eventually. -/
theorem exteriorOmittedAtScale_mem_of_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℕ → ℝ} {w : ℕ → ℂ} {v : ℂ}
    (hs : Tendsto s atTop (𝓝 (1 : ℝ)))
    (hw : ∀ᶠ n in atTop, w n ∈ exteriorOmittedAtScale F (s n))
    (hv : Tendsto w atTop (𝓝 v)) : v ∈ exteriorOmitted F := by
  rw [← exteriorOmitted_eq_iInter_scaleSeq F]
  apply Set.mem_iInter.mpr
  intro j
  have htail : ∀ᶠ n in atTop,
      w n ∈ exteriorOmittedAtScale F (omittedScaleSeq j) := by
    filter_upwards [hw,hs.eventually (Ioi_mem_nhds (omittedScaleSeq_lt_one j))]
      with n hwn hsn
    exact exteriorOmittedAtScale_antitone F (omittedScaleSeq_pos j) hsn.le hwn
  exact (exteriorOmittedAtScale_isCompact F hc
    (omittedScaleSeq_pos j) (omittedScaleSeq_lt_one j)).isClosed.mem_of_tendsto hv htail

/-- The same closed-graph property for the actual omitted sets of F_s.
The scaling is removed explicitly, rather than confusing K_s with sK_s. -/
theorem exteriorOmitted_rescale_mem_of_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℕ → ℝ} {w : ℕ → ℂ} {v : ℂ}
    (hs : Tendsto s atTop (𝓝 (1 : ℝ)))
    (hw : ∀ᶠ n in atTop, w n ∈ exteriorOmitted (rescaleExterior (s n) F))
    (hv : Tendsto w atTop (𝓝 v)) : v ∈ exteriorOmitted F := by
  have hsC : Tendsto (fun n => (s n : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def,Complex.ofReal_one] using
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hs
  have hw' : ∀ᶠ n in atTop,
      (s n : ℂ)⁻¹*w n ∈ exteriorOmittedAtScale F (s n) := by
    filter_upwards [hw,hs.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hwn hsn
    rw [rescaleExterior_omitted_eq_image F hsn] at hwn
    obtain ⟨z,hz,hzw⟩ := hwn
    have hsnC : (s n : ℂ) ≠ 0 := by exact_mod_cast hsn.ne'
    simpa only [← hzw,← mul_assoc,inv_mul_cancel₀ hsnC,one_mul] using hz
  have hv' : Tendsto (fun n => (s n : ℂ)⁻¹*w n) atTop (𝓝 v) := by
    simpa only [inv_one,one_mul] using (hsC.inv₀ (by norm_num)).mul hv
  exact exteriorOmittedAtScale_mem_of_tendsto F hc hs hw' hv'

end SpringerLean
