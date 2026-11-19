import SpringerLean.Round2134DiskToNormalizedExterior
import SpringerLean.Round2129EvenFilledNormalizedFactor

open Set

namespace SpringerLean

private theorem reciprocalExteriorDomain_neg_mem
    (K : Set ℂ) (k : ℕ) (hk : 0 < k) (hK : EvenGeneratorInvariant (continuumFill K) k)
    (z : ℂ) (hz : z ∈ reciprocalExteriorDomain K 0) :
    -z ∈ reciprocalExteriorDomain K 0 := by
  by_cases hz0 : z = 0
  · simpa only [hz0,neg_zero] using hz
  have hr := evenGeneratorInvariant_to_evenRotationInvariant (continuumFill K) k hk hK
  have hpow : (-1:ℂ)^(2*k) = 1 := by rw [pow_mul]; norm_num
  have hn := (mem_reciprocalExteriorDomain_iff K 0 z hz0).mp hz
  apply (mem_reciprocalExteriorDomain_iff K 0 (-z) (neg_ne_zero.mpr hz0)).mpr
  simp only [zero_add,inv_neg,mem_compl_iff] at hn ⊢
  intro h
  exact hn (by simpa only [neg_one_mul,neg_neg] using hr (-1) (-z⁻¹) hpow h)

private theorem rotate_exterior_image_of_scale
    (F : ℂ → ℂ) (K : Set ℂ) (a η : ℂ) (hη : ‖η‖ = 1)
    (hIm : F '' exteriorDisk = (continuumScale K a)ᶜ) :
    rotateCenteredExterior F η '' exteriorDisk = (continuumScale K (η⁻¹*a))ᶜ := by
  have hη0 : η ≠ 0 := by intro h; simp [h] at hη
  have hi : ‖η⁻¹‖ = 1 := by simp only [norm_inv,hη,inv_one]
  have hm (c : ℂ) (hc : ‖c‖ = 1) (w : ℂ) (hw : w ∈ exteriorDisk) : c*w ∈ exteriorDisk := by
    change 1 < ‖c*w‖
    simpa only [norm_mul,hc,one_mul] using (show 1 < ‖w‖ from hw)
  have he (z : ℂ) : z ∈ continuumScale K (η⁻¹*a) ↔ η*z ∈ continuumScale K a := by
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u,hu,by simp only [←mul_assoc,mul_inv_cancel₀ hη0,one_mul]⟩
    · rintro ⟨u,hu,hu'⟩
      refine ⟨u,hu,?_⟩
      change a*u = η*z at hu'
      change (η⁻¹*a)*u = z
      rw [mul_assoc,hu',←mul_assoc,inv_mul_cancel₀ hη0,one_mul]
  apply Subset.antisymm
  · rintro _ ⟨w,hw,rfl⟩
    have hF : F (η*w) ∉ continuumScale K a := by
      rw [←mem_compl_iff,←hIm]
      exact ⟨η*w,hm η hη w hw,rfl⟩
    intro h
    have H := (he (rotateCenteredExterior F η w)).mp h
    apply hF
    simpa only [rotateCenteredExterior,←mul_assoc,mul_inv_cancel₀ hη0,one_mul] using H
  · intro z hz
    have hn : η*z ∈ F '' exteriorDisk := by
      rw [hIm]
      exact fun h => hz ((he z).mpr h)
    obtain ⟨w,hw,hFw⟩ := hn
    refine ⟨η⁻¹*w,hm η⁻¹ hi w hw,?_⟩
    rw [rotateCenteredExterior,←mul_assoc,mul_inv_cancel₀ hη0,one_mul,hFw,
      ←mul_assoc,inv_mul_cancel₀ hη0,one_mul]

/-- Disk uniformization on the reciprocal domains gives the centered
positive-scale exterior normalization required by the even comparison. -/
theorem evenContinuum_normalized_exterior_of_reciprocalDiskUniformization
    (K : Set ℂ) (hK : IsCompact K) (k : ℕ) (hk : 0 < k) (hrot : EvenGeneratorInvariant K k)
    (u : ℂ) (hu : u ∈ K)
    (hU : ∀ a ∈ continuumFill K, Nonempty (ReciprocalDiskUniformization K a)) :
    ∃ (r : ℝ) (F : ℂ → ℂ), 0 < r ∧ CenteredExteriorUnivalent F ∧
      F '' exteriorDisk = (continuumScale (continuumFill K) (r:ℂ))ᶜ := by
  let C := continuumFill K
  let η := Complex.exp (2*Real.pi*Complex.I/((2*k:ℕ):ℂ))
  have hp : IsPrimitiveRoot η (2*k) := Complex.isPrimitiveRoot_exp _ (by omega)
  have hη0 : η ≠ 0 := by
    intro h
    have H := hp.pow_eq_one
    rw [h,zero_pow (by omega : 2*k ≠ 0)] at H
    exact zero_ne_one H
  have hη1 : η ≠ 1 := hp.ne_one (by omega)
  have hCrot := continuumFill_evenGeneratorInvariant K k hk hrot
  have hR := evenGeneratorInvariant_to_evenRotationInvariant C k hk hCrot
  have hηR (z : ℂ) : η*z ∈ C ↔ z ∈ C := by
    refine ⟨fun h => ?_,hR η z hp.pow_eq_one⟩
    have hpow : (η⁻¹)^(2*k) = 1 := by rw [inv_pow,hp.pow_eq_one,inv_one]
    simpa only [←mul_assoc,inv_mul_cancel₀ hη0,one_mul] using hR η⁻¹ (η*z) hpow h
  have huC := subset_continuumFill K hu
  obtain ⟨fu⟩ := hU u huC
  have h0 := zero_mem_continuumFill_of_reciprocalDiskUniformization K hK u η huC hη0 hη1 hηR fu
  obtain ⟨f⟩ := hU 0 h0
  have hOdd := reciprocalDiskUniformization_odd K 0 f (reciprocalExteriorDomain_neg_mem K k hk hCrot)
  obtain ⟨a,G,ha,hG,hIm⟩ := reciprocalDiskUniformization_to_centered_exterior K h0 f hOdd
  let r := ‖a‖
  let c := a/(r:ℂ)
  have hr : 0 < r := norm_pos_iff.mpr ha
  have hr0 : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc : ‖c‖ = 1 := by
    rw [show c = a/(r:ℂ) from rfl,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact div_self hr.ne'
  refine ⟨r,rotateCenteredExterior G c,hr,rotateCenteredExterior_centeredExteriorUnivalent G hG c hc,?_⟩
  have hca : c⁻¹*a = (r:ℂ) := by dsimp [c]; field_simp [ha,hr0]
  simpa only [hca] using rotate_exterior_image_of_scale G C a c hc hIm

end SpringerLean
