import SpringerLean.Round2127EvenActualNormalizedFactor
import SpringerLean.Round2128RegularStarEmptyInterior

open Set Real

namespace SpringerLean

/-- The even conclusion for an arbitrary normalized continuum once its
external map is provided. Filling is used internally and the final
equality concerns the original continuum, including any holes. -/
theorem evenStar_filled_normalized_factorConstant
    (K : Set ℂ) (hK : IsCompact K) (hc : IsConnected K) (k : ℕ) (hk : 0 < k)
    (hrot : EvenGeneratorInvariant K k) (u v : ℂ) (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v)
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (hIm : F '' exteriorDisk = (continuumFill K)ᶜ) :
    let S := regularStarRaySet (2*k)
    factorConstant K ≤ factorConstant S ∧
      (1-(k:ℝ)^2*‖exteriorForwardCoeff F (2*k-1)‖^2)/(96*(k:ℝ)^2) ≤
        log (factorConstant S/factorConstant K) ∧
      (factorConstant K = factorConstant S ↔
        ∃ b : ℂ, ‖b‖ = 1 ∧ K = (fun z : ℂ => b*z) '' S) := by
  let S := regularStarRaySet (2*k)
  have hcC := continuumFill_isConnected K hK.isClosed hc
  have hrC := continuumFill_evenGeneratorInvariant K k hk hrot
  have hsub := subset_continuumFill K
  have he := factorConstant_fill_eq K hK hc.nonempty
  obtain ⟨hle,hgap,hiff⟩ := evenStar_actual_normalized_factorConstant F (continuumFill K) k hk hF hcC hrC
    hIm u v (hsub hu) (hsub hv) huv
  rw [he] at hle hgap hiff
  refine ⟨hle,hgap,?_⟩
  constructor
  · intro h
    obtain ⟨b,hb,hset⟩ := hiff.mp h
    have hb0 : b ≠ 0 := by intro h; simp [h] at hb
    have hi : interior (continuumFill K) = ∅ := by
      rw [hset]
      exact regularStarRaySet_scale_interior_empty (2*k) (by omega) b hb0
    have hs := continuumFill_eq_self_if_interior_empty K hK.isClosed hi
    exact ⟨b,hb,hs.symm.trans hset⟩
  · rintro ⟨b,hb,hset⟩
    have hb0 : b ≠ 0 := by intro h; simp [h] at hb
    rw [hset]
    exact factorConstant_scale S b hb0

end SpringerLean
