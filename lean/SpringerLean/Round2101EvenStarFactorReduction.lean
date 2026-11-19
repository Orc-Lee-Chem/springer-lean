import SpringerLean.Round2100EvenStarRadialFactorBaseline
import SpringerLean.Round1953FactorScaling

open MeasureTheory Set Real

namespace SpringerLean

private theorem evenStar_log_radius_mean
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F) (hK : EvenGeneratorInvariant K k)
    (hIm : F '' exteriorDisk = Kᶜ) :
    let G := evenExteriorPowerQuotient F k
    (∫ z, log (evenStarRadius k+‖z‖) ∂actualExteriorBoundaryProbability F) =
      log (evenStarRadius k) +
        (∫ z, evenStarCorrectedRadialTest k ‖z‖ ∂actualExteriorBoundaryProbability G) +
        actualBoundaryRadialMoment G 2/(64*(k:ℝ)^2) := by
  let G := evenExteriorPowerQuotient F k
  let μ := actualExteriorBoundaryProbability F
  let H (z : ℂ) := evenStarCorrectedRadialTest k ‖z‖
  let V (z : ℂ) := ‖z‖^2
  have hμ : IsProbabilityMeasure μ := ⟨actualExteriorBoundaryProbability_univ F hF⟩
  have hG := evenExteriorPowerQuotient_actual_centered F K k hk hF hK hIm
  have hH : Continuous H := (evenStarCorrectedRadialTest_continuous k).comp continuous_norm
  have hV : Continuous V := continuous_norm.pow 2
  have hiH : Integrable (fun z => H (z^k)) μ :=
    actualExteriorBoundaryProbability_integrable_of_continuous F hF _ (hH.comp (by fun_prop))
  have hiV : Integrable (fun z => V (z^k)) μ :=
    actualExteriorBoundaryProbability_integrable_of_continuous F hF _ (hV.comp (by fun_prop))
  have hiL : Integrable (fun z => log (evenStarRadius k) + H (z^k)) μ :=
    (integrable_const _).add hiH
  change (∫ z, log (evenStarRadius k+‖z‖) ∂μ) = _
  simp_rw [evenStar_log_radius_add_norm_eq_corrected k hk]
  change (∫ z, log (evenStarRadius k) + H (z^k) + V (z^k)/(64*(k:ℝ)^2) ∂μ) = _
  rw [integral_add hiL (hiV.div_const (64*(k:ℝ)^2)),
    integral_add (integrable_const (log (evenStarRadius k))) hiH, integral_const, probReal_univ, one_smul,
    integral_div]
  rw [evenPowerQuotient_actual_boundary_probability_integral F K k hk hF hK hIm H hH,
    evenPowerQuotient_actual_boundary_probability_integral F K k hk hF hK hIm V hV]
  exact congrArg (fun x : ℝ => log (evenStarRadius k) + (∫ z, H z ∂actualExteriorBoundaryProbability G) +
    x/(64*(k:ℝ)^2)) (actualExteriorBoundaryProbability_integral_norm_sq G hG)

private theorem evenStar_log_farthest_mean_le
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F) (hK : EvenGeneratorInvariant K k)
    (hIm : F '' exteriorDisk = Kᶜ)
    (u v : ℂ) (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v) :
    (∫ z, log (continuumFarthestDistance K z) ∂actualExteriorBoundaryProbability F) ≤
      ∫ z, log (evenStarRadius k+‖z‖) ∂actualExteriorBoundaryProbability F := by
  have heq : exteriorOmitted F = K := by
    change (F '' exteriorDisk)ᶜ = K
    rw [hIm,compl_compl]
  have hcomp := heq ▸ exteriorOmitted_isCompact F hF
  have hd := continuumFarthestDistance_pos_of_two_points K hcomp u v hu hv huv
  have hdc := (continuumFarthestDistance_continuous K hcomp ⟨u,hu⟩).log (fun z => (hd z).ne')
  have hlc : Continuous (fun z : ℂ => log (evenStarRadius k+‖z‖)) :=
    (continuous_const.add continuous_norm).log (fun z => (add_pos_of_pos_of_nonneg
      (evenStarRadius_pos k) (norm_nonneg z)).ne')
  apply integral_mono (actualExteriorBoundaryProbability_integrable_of_continuous F hF _ hdc)
    (actualExteriorBoundaryProbability_integrable_of_continuous F hF _ hlc)
  intro z
  exact Real.log_le_log (hd z) (evenStar_farthestDistance_le_of_radius K hcomp ⟨u,hu⟩ _
    (evenStar_omitted_norm_le_radius F K k hk hF hK hIm) z)

/-- For a normalized actual even-symmetric map, the remaining Green
comparison implies the entire factor-constant conclusion, including
the quantitative bound and both equality directions. -/
theorem evenStar_factorConstant_of_green_comparison
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F) (hK : EvenGeneratorInvariant K k)
    (hIm : F '' exteriorDisk = Kᶜ)
    (u v : ℂ) (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v)
    (hcomp : ∀ r > 0,
      circleAverage (exteriorGreenCoordinate (evenExteriorPowerQuotient F k)) 0 r ≤
        circleAverage (exteriorGreenCoordinate
          (evenExteriorPowerQuotient (oddStarPerturbation (2*k) 0) k)) 0 r) :
    let S := regularStarRaySet (2*k)
    factorConstant K ≤ factorConstant S ∧
      (1-(k:ℝ)^2*‖exteriorForwardCoeff F (2*k-1)‖^2)/(96*(k:ℝ)^2) ≤
        log (factorConstant S/factorConstant K) ∧
      (factorConstant K = factorConstant S ↔
        ∃ b : ℂ, ‖b‖ = 1 ∧ K = (fun z : ℂ => b*z) '' S) := by
  let S := regularStarRaySet (2*k)
  let Fs := oddStarPerturbation (2*k) 0
  let G := evenExteriorPowerQuotient F k
  let Gs := evenExteriorPowerQuotient Fs k
  let μ := actualExteriorBoundaryProbability F
  let ν := actualExteriorBoundaryProbability Fs
  let J := ∫ z, log (continuumFarthestDistance K z) ∂μ
  let Js := ∫ z, log (continuumFarthestDistance S z) ∂ν
  let L := log (factorConstant S/factorConstant K)
  obtain ⟨hFs,hSIm,hS⟩ := regularEvenStar_omitted_and_invariant k hk
  have hO : exteriorOmitted F = K := by change (F '' exteriorDisk)ᶜ = K; rw [hIm,compl_compl]
  have hOs : exteriorOmitted Fs = S := by change (Fs '' exteriorDisk)ᶜ = S; rw [hSIm,compl_compl]
  have hG := evenExteriorPowerQuotient_actual_centered F K k hk hF hK hIm
  have hGs := evenExteriorPowerQuotient_actual_centered Fs S k hk hFs hS hSIm
  obtain ⟨x,y,hx,hy,hxy⟩ := (oddStarPerturbation_actual_continuum (2*k) (by omega) 0 (by norm_num)).2.2.1
  have hfactor : factorConstant K = exp J := by
    change factorConstant K = exp (∫ z, log (continuumFarthestDistance K z) ∂μ)
    rw [← hO]
    exact factorConstant_eq_actual_farthest_exp F hF u v (hO.symm ▸ hu) (hO.symm ▸ hv) huv
  have hstar : factorConstant S = exp Js := by
    change factorConstant S = exp (∫ z, log (continuumFarthestDistance S z) ∂ν)
    rw [← hOs]
    exact factorConstant_eq_actual_farthest_exp Fs hFs x y hx hy hxy
  have hLee : L = Js-J := by
    change log (factorConstant S/factorConstant K) = _
    rw [hfactor,hstar, ← Real.exp_sub, Real.log_exp]
  have hJs : Js = ∫ z, log (evenStarRadius k+‖z‖) ∂ν := by
    have hs : S ∈ ae ν := hOs ▸ actualExteriorBoundaryProbability_ae_mem_omitted Fs hFs
      (exteriorOmitted_isCompact Fs hFs).isClosed
    apply integral_congr_ae
    filter_upwards [hs] with z hz
    rw [evenStar_regular_farthestDistance k hk z hz]
  have hJ := evenStar_log_farthest_mean_le F K k hk hF hK hIm u v hu hv huv
  change J ≤ ∫ z, log (evenStarRadius k+‖z‖) ∂μ at hJ
  have hlog := evenStarCorrectedRadialTest_integral_le_of_green_comparison G Gs hG hGs k hk hcomp
  have hmargin : (2-actualBoundaryRadialMoment G 2)/(64*(k:ℝ)^2) ≤ L := by
    rw [evenStar_log_radius_mean F K k hk hF hK hIm] at hJ
    rw [evenStar_log_radius_mean Fs S k hk hFs hS hSIm, regularEvenStar_powerQuotient_secondMoment k hk] at hJs
    rw [hLee, sub_div]
    linarith only [hJ,hJs,hlog]
  have hquant := evenStar_actual_factor_gap_of_potential_comparison F K k hk hF hK hIm L hmargin
  have hQ2 := actualBoundaryRadialMoment_two_margin G hG
  have hb : ‖exteriorForwardCoeff G 1‖ ≤ 1 := by
    have h := exteriorInverseCoeff_one_norm_le G hG
    rwa [exteriorInverseCoeff_one_eq_forwardCoeff_one G hG] at h
  have hR : actualBoundaryRadialMoment G 2 ≤ 2 := by
    nlinarith [norm_nonneg (exteriorForwardCoeff G 1)]
  have hL : 0 ≤ L := (div_nonneg (sub_nonneg.mpr hR) (by positivity)).trans hmargin
  refine ⟨?_, hquant, ?_⟩
  · rw [hfactor,hstar]
    apply Real.exp_le_exp.mpr
    linarith only [hL,hLee]
  constructor
  · intro he
    have hzero : L = 0 := by
      change log (factorConstant S/factorConstant K) = 0
      rw [he,hstar,div_self (exp_pos _).ne',Real.log_one]
    obtain ⟨a,ha,hr⟩ := evenStar_actual_factor_gap_zero_equality_set_of_potential_comparison
      F K k hk hF hK hIm L hmargin hzero
    obtain ⟨b,hb,hbr⟩ := even_slit_power_preimage_similar_regularStar k hk a ha
    exact ⟨b,hb,by rw [hr,hbr,regularStarPowerSet_eq_raySet _ (by omega)]⟩
  · rintro ⟨b,hb,himg⟩
    rw [himg]
    have hbn : b ≠ 0 := by intro h; simp [h] at hb
    exact factorConstant_scale S b hbn

end SpringerLean
