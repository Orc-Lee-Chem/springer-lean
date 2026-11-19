import SpringerLean.Round2135EvenContinuumNormalization

open Set Real

namespace SpringerLean

/-- The continuum argument requires only existence of the disk mapping
on its reciprocal domains. The normalized map, inequality, forward
coefficient deficit and similarity classification follow from it. -/
theorem evenContinuum_factorConstant_of_reciprocalDiskUniformization
    (K : Set ℂ) (hK : IsCompact K) (hc : IsConnected K) (k : ℕ) (hk : 0 < k)
    (hrot : EvenGeneratorInvariant K k) (u v : ℂ) (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v)
    (hU : ∀ a ∈ continuumFill K, Nonempty (ReciprocalDiskUniformization K a)) :
    let S := regularStarRaySet (2*k)
    ∃ (r : ℝ) (F : ℂ → ℂ), 0 < r ∧ CenteredExteriorUnivalent F ∧
      F '' exteriorDisk = (continuumScale (continuumFill K) (r:ℂ))ᶜ ∧
      factorConstant K ≤ factorConstant S ∧
      (1-(k:ℝ)^2*‖exteriorForwardCoeff F (2*k-1)‖^2)/(96*(k:ℝ)^2) ≤
        log (factorConstant S/factorConstant K) ∧
      (factorConstant K = factorConstant S ↔
        ∃ b : ℂ, b ≠ 0 ∧ K = continuumScale S b) := by
  let S := regularStarRaySet (2*k)
  let C := continuumFill K
  obtain ⟨r,F,hr,hF,hIm⟩ :=
    evenContinuum_normalized_exterior_of_reciprocalDiskUniformization K hK k hk hrot u hu hU
  let a : ℂ := (r:ℂ)
  let L := continuumScale C a
  have ha0 : a ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hcont : Continuous (fun z : ℂ => a*z) := continuous_const.mul continuous_id
  have hcL : IsConnected L := (continuumFill_isConnected K hK.isClosed hc).image _ hcont.continuousOn
  have hrC := continuumFill_evenGeneratorInvariant K k hk hrot
  have hrL : EvenGeneratorInvariant L k := by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := hw
    exact ⟨z * Complex.exp (2 * Real.pi * Complex.I / ((2*k:ℕ):ℂ)),
      by simpa only [mul_comm] using hrC z hz, by ring⟩
  have hsub := subset_continuumFill K
  have huL : a*u ∈ L := ⟨u,hsub hu,rfl⟩
  have hvL : a*v ∈ L := ⟨v,hsub hv,rfl⟩
  have huvL : a*u ≠ a*v := fun h => huv (mul_left_cancel₀ ha0 h)
  have hL : factorConstant L = factorConstant K :=
    (factorConstant_scale C a ha0).trans (factorConstant_fill_eq K hK hc.nonempty)
  obtain ⟨hle,hgap,hiff⟩ :=
    evenStar_actual_normalized_factorConstant F L k hk hF hcL hrL hIm _ _ huL hvL huvL
  rw [hL] at hle hgap hiff
  refine ⟨r,F,hr,hF,hIm,hle,hgap,?_⟩
  constructor
  · intro h
    obtain ⟨b,hb,hset⟩ := hiff.mp h
    have hb0 : b ≠ 0 := fun hb0 => by simp [hb0] at hb
    let c := a⁻¹*b
    have hc0 : c ≠ 0 := mul_ne_zero (inv_ne_zero ha0) hb0
    have hC : C = continuumScale S c := by
      rw [←continuumScale_scale_inv C a ha0]
      change continuumScale L a⁻¹ = continuumScale S c
      rw [show L = continuumScale S b from hset]
      simp only [continuumScale, image_image, c, mul_assoc]
    have hi : interior C = ∅ := by
      rw [hC]
      exact regularStarRaySet_scale_interior_empty (2*k) (by omega) c hc0
    have hself := continuumFill_eq_self_if_interior_empty K hK.isClosed hi
    exact ⟨c,hc0,hself.symm.trans hC⟩
  · rintro ⟨b,hb,rfl⟩
    exact factorConstant_scale S b hb

end SpringerLean
