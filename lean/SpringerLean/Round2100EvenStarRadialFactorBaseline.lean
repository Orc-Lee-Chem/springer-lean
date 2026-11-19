import SpringerLean.Round2099EvenStarFarthestGeometry

open MeasureTheory Set Filter Real
open scoped Topology

namespace SpringerLean

theorem actualExteriorBoundaryProbability_integrable_of_continuous
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (f : ℂ → ℝ) (hf : Continuous f) :
    Integrable f (actualExteriorBoundaryProbability F) := by
  let μ := actualExteriorBoundaryProbability F
  have hprob : IsProbabilityMeasure μ := ⟨actualExteriorBoundaryProbability_univ F hF⟩
  have hK := exteriorOmitted_isCompact F hF
  have hs := actualExteriorBoundaryProbability_ae_mem_omitted F hF hK.isClosed
  obtain ⟨C,hC⟩ := (hK.image hf).isBounded.exists_norm_le
  apply Integrable.mono (integrable_const (max C 0)) hf.aestronglyMeasurable
  filter_upwards [hs] with z hz
  rw [Real.norm_of_nonneg (le_max_right C 0)]
  exact (hC _ ⟨z,hz,rfl⟩).trans (le_max_left _ _)

theorem actualExteriorBoundaryProbability_integral_norm_sq
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) :
    (∫ z, ‖z‖^2 ∂actualExteriorBoundaryProbability F) = actualBoundaryRadialMoment F 2 := by
  unfold actualExteriorBoundaryProbability actualExteriorBoundaryMeasure actualBoundaryRadialMoment
  rw [integral_smul_measure, integral_map (actualExteriorRadialTrace_aestronglyMeasurable F hF).aemeasurable
    (show Continuous (fun z : ℂ => ‖z‖^2) by fun_prop).aestronglyMeasurable]
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr Real.two_pi_pos.le),smul_eq_mul]
  simp only [Real.rpow_two]

theorem evenPowerQuotient_actual_boundary_probability_pushforward
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F) (hK : EvenGeneratorInvariant K k)
    (hIm : F '' exteriorDisk = Kᶜ) :
    (actualExteriorBoundaryProbability F).map (fun z : ℂ => z^k) =
      actualExteriorBoundaryProbability (evenExteriorPowerQuotient F k) := by
  unfold actualExteriorBoundaryProbability
  rw [Measure.map_smul _ (show Measurable (fun z : ℂ => z^k) by fun_prop).aemeasurable,
    evenPowerQuotient_actual_boundary_measure_pushforward F K k hk hF hK hIm]

theorem evenPowerQuotient_actual_boundary_probability_integral
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F) (hK : EvenGeneratorInvariant K k)
    (hIm : F '' exteriorDisk = Kᶜ) (f : ℂ → ℝ) (hf : Continuous f) :
    (∫ z, f (z^k) ∂actualExteriorBoundaryProbability F) =
      ∫ z, f z ∂actualExteriorBoundaryProbability (evenExteriorPowerQuotient F k) := by
  rw [← evenPowerQuotient_actual_boundary_probability_pushforward F K k hk hF hK hIm,
    integral_map (show Measurable (fun z : ℂ => z^k) by fun_prop).aemeasurable hf.aestronglyMeasurable]

theorem regularEvenStar_omitted_and_invariant (k : ℕ) (hk : 0 < k) :
    let F := oddStarPerturbation (2*k) 0
    let S := regularStarRaySet (2*k)
    CenteredExteriorUnivalent F ∧ F '' exteriorDisk = Sᶜ ∧ EvenGeneratorInvariant S k := by
  let F := oddStarPerturbation (2*k) 0
  let S := regularStarRaySet (2*k)
  have hk2 : 2 ≤ 2*k := by omega
  have hF := oddStarPerturbation_centeredExteriorUnivalent (2*k) hk2 0 (by norm_num)
  have hO : exteriorOmitted F = S := oddStarPerturbation_zero_omitted_eq_regularStarRays (2*k) hk2
  refine ⟨hF,?_ ,?_⟩
  · change F '' exteriorDisk = Sᶜ
    rw [←hO,exteriorOmitted,compl_compl]
  · let ζ : ℂ := Complex.exp (2*Real.pi*Complex.I/((2*k : ℕ):ℂ))
    have hζ : IsPrimitiveRoot ζ (2*k) := Complex.isPrimitiveRoot_exp _ (by omega)
    intro z hz
    change z ∈ S at hz
    change ζ*z ∈ S
    rw [←hO] at hz ⊢
    exact (oddStarPerturbation_omitted_rotation_iff (2*k) hk2 0 (by norm_num)
      ζ z hζ.pow_eq_one).2 hz

theorem regularEvenStar_powerQuotient_eqOn_slit (k : ℕ) (hk : 0 < k) :
    EqOn (evenExteriorPowerQuotient (oddStarPerturbation (2*k) 0) k) (slitMap 1) exteriorDisk := by
  let F := oddStarPerturbation (2*k) 0
  let S := regularStarRaySet (2*k)
  obtain ⟨hF,hIm,hS⟩ := regularEvenStar_omitted_and_invariant k hk
  have hg := evenExteriorPowerQuotient_actual_centered F S k hk hF hS hIm
  have hgeom := (evenExteriorPowerQuotient_actual_geometry F S k hk hF hS hIm).2.1
  have hpow : (fun z : ℂ => z^k) '' S = (slitMap 1 '' exteriorDisk)ᶜ := by
    have hS' : S = (fun z : ℂ => z^k) ⁻¹' (slitMap 1 '' exteriorDisk)ᶜ := by
      change regularStarRaySet (2*k) = {z : ℂ | z^k ∈ (slitMap 1 '' exteriorDisk)ᶜ}
      rw [even_slit_power_preimage_eq_regularStarPowerSet,
        regularStarPowerSet_eq_raySet (2*k) (by omega)]
    rw [hS',image_preimage_eq _ (fun z => IsAlgClosed.exists_pow_nat_eq z hk)]
  rw [hpow,compl_compl] at hgeom
  exact centeredExteriorUnivalent_eqOn_of_same_image _ _ hg
    (slitMap_centeredExteriorUnivalent 1 (by simp)) hgeom

theorem regularEvenStar_powerQuotient_secondMoment (k : ℕ) (hk : 0 < k) :
    actualBoundaryRadialMoment (evenExteriorPowerQuotient (oddStarPerturbation (2*k) 0) k) 2 = 2 := by
  obtain ⟨hF,hIm,hS⟩ := regularEvenStar_omitted_and_invariant k hk
  have hg := evenExteriorPowerQuotient_actual_centered _ _ k hk hF hS hIm
  exact (actualBoundaryRadialMoment_eq_of_eqOn_slit _ hg 1 (by simp)
    (regularEvenStar_powerQuotient_eqOn_slit k hk) 2 (by norm_num)).trans slitRadialMomentConstant_two

end SpringerLean
