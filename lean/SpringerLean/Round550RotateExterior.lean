import SpringerLean.Round484RootOmittedSet
import SpringerLean.Round39RotateExterior

open scoped Topology

namespace SpringerLean
set_option Elab.async false

theorem rotateExterior_forwardGerm_of_ne_zero (a : ℂ) (ha : a ≠ 0) (F : ℂ → ℂ) :
    exteriorForwardGerm (rotateExterior a F) =
      fun u => a⁻¹ * exteriorForwardGerm F (a⁻¹ * u) := by
  funext u
  by_cases hu : u = 0
  · simp [hu, exteriorForwardGerm_zero]
  have hau : a⁻¹ * u ≠ 0 := mul_ne_zero (inv_ne_zero ha) hu
  rw [exteriorForwardGerm_punctured _ hu, exteriorForwardGerm_punctured _ hau]
  dsimp only [rotateExterior]
  rw [mul_inv_rev, inv_inv]
  have he : u⁻¹ * a = a * u⁻¹ := mul_comm _ _
  rw [he]
  field_simp [ha, hu] <;> ring

theorem rotateExterior_omitted_iff
    (F : ℂ → ℂ) (a : ℂ) (ha : ‖a‖ = 1) (w : ℂ) :
    w ∈ exteriorOmitted (rotateExterior a F) ↔ a * w ∈ exteriorOmitted F := by
  have ha0 : a ≠ 0 := by intro he; simp [he] at ha
  have hainv : ‖a⁻¹‖ = 1 := by rw [norm_inv, ha, inv_one]
  constructor
  · intro hw him
    obtain ⟨v, hv, hF⟩ := him
    have hsrc : a⁻¹ * v ∈ exteriorDisk := by
      change 1 < ‖a⁻¹ * v‖
      rw [norm_mul, hainv, one_mul]
      exact hv
    apply hw
    refine ⟨a⁻¹ * v, hsrc, ?_⟩
    simp [rotateExterior, mul_assoc, ha0, hF]
  · intro hw him
    obtain ⟨z, hz, he⟩ := him
    have hsrc : a * z ∈ exteriorDisk := by
      change 1 < ‖a * z‖
      rw [norm_mul, ha, one_mul]
      exact hz
    apply hw
    refine ⟨a * z, hsrc, ?_⟩
    have h := congrArg (fun q : ℂ => a * q) he
    simpa [rotateExterior, mul_assoc, ha0] using h

end SpringerLean
