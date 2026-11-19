import SpringerLean.Round2023EvenGeneratorSymmetry

namespace SpringerLean

/-- Rotates domain and range together, preserving the leading coefficient. -/
noncomputable def rotateCenteredExterior (F : ℂ → ℂ) (η : ℂ) (z : ℂ) : ℂ :=
  η⁻¹ * F (η*z)

theorem rotateCenteredExterior_germ
    (F : ℂ → ℂ) (η : ℂ) (hη : η ≠ 0) (t : ℂ) :
    exteriorForwardGerm (rotateCenteredExterior F η) t =
      η⁻¹ * exteriorForwardGerm F (η⁻¹*t) := by
  by_cases ht : t = 0
  · simp [ht, exteriorForwardGerm]
  · have hηt : η⁻¹*t ≠ 0 := mul_ne_zero (inv_ne_zero hη) ht
    simp only [exteriorForwardGerm, ht, hηt, ↓reduceIte,
      rotateCenteredExterior]
    field_simp

theorem rotateCenteredExterior_centeredExteriorUnivalent
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (η : ℂ) (hη : ‖η‖ = 1) :
    CenteredExteriorUnivalent (rotateCenteredExterior F η) := by
  have hη0 : η ≠ 0 := by
    intro h; simp [h] at hη
  have hηz (z : ℂ) (hz : z ∈ exteriorDisk) : η*z ∈ exteriorDisk := by
    change 1 < ‖η*z‖
    rw [norm_mul, hη, one_mul]
    exact hz
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hF := hc.1.differentiableAt
      (exteriorDisk_isOpen.mem_nhds (hηz z hz))
    have hlin : DifferentiableAt ℂ (fun w : ℂ => η*w) z := by fun_prop
    have hcomp : DifferentiableAt ℂ (fun w : ℂ => F (η*w)) z :=
      hF.comp z hlin
    exact (hcomp.const_mul η⁻¹).differentiableWithinAt
  · intro z hz w hw heq
    have hFeq : F (η*z) = F (η*w) := by
      change η⁻¹ * F (η*z) = η⁻¹ * F (η*w) at heq
      exact mul_left_cancel₀ (inv_ne_zero hη0) heq
    have hzw := hc.2.1 (hηz z hz) (hηz w hw) hFeq
    exact mul_left_cancel₀ hη0 hzw
  · have hlin : AnalyticAt ℂ (fun t : ℂ => η⁻¹*t) 0 := by fun_prop
    have hcomp : AnalyticAt ℂ
        (fun t : ℂ => exteriorForwardGerm F (η⁻¹*t)) 0 := by
      have hF0 : AnalyticAt ℂ (exteriorForwardGerm F) ((fun t : ℂ => η⁻¹*t) 0) := by
        simpa using hc.2.2
      exact hF0.comp hlin
    have hmul : AnalyticAt ℂ
        (fun t : ℂ => η⁻¹ * exteriorForwardGerm F (η⁻¹*t)) 0 :=
      analyticAt_const.mul hcomp
    have heq : exteriorForwardGerm (rotateCenteredExterior F η) =
        fun t : ℂ => η⁻¹ * exteriorForwardGerm F (η⁻¹*t) := by
      funext t
      exact rotateCenteredExterior_germ F η hη0 t
    rw [heq]
    exact hmul

end SpringerLean

#print axioms SpringerLean.rotateCenteredExterior_germ
#print axioms SpringerLean.rotateCenteredExterior_centeredExteriorUnivalent
