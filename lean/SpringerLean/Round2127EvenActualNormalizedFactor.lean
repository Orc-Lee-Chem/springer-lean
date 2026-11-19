import SpringerLean.Round2126OddGreenCircularComparison
import SpringerLean.Round2101EvenStarFactorReduction

open Set Real

namespace SpringerLean

theorem exteriorGreenCoordinate_congr_exterior
    (F G : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (hG : CenteredExteriorUnivalent G)
    (h : EqOn F G exteriorDisk) : exteriorGreenCoordinate F = exteriorGreenCoordinate G := by
  classical
  have him : F '' exteriorDisk = G '' exteriorDisk := h.image_eq
  funext z
  by_cases hz : z ∈ F '' exteriorDisk
  · have hzg : z ∈ G '' exteriorDisk := him ▸ hz
    obtain ⟨w,hw,rfl⟩ := hz
    have hfg : F w = G w := h hw
    have hf : exteriorInverse F (F w) = w := hF.2.1.leftInvOn_invFunOn hw
    have hg : exteriorInverse G (F w) = w := hfg ▸ hG.2.1.leftInvOn_invFunOn hw
    rw [exteriorGreenCoordinate,if_pos ⟨w,hw,rfl⟩,exteriorGreenCoordinate,if_pos hzg,hf,hg]
  · have hzg : z ∉ G '' exteriorDisk := by rwa [←him]
    simp [exteriorGreenCoordinate,hz,hzg]

/-- The normalized even-star factor theorem for an actual centered
exterior map, on its actual connected omitted set. -/
theorem evenStar_actual_normalized_factorConstant
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F) (hconn : IsConnected K) (hK : EvenGeneratorInvariant K k)
    (hIm : F '' exteriorDisk = Kᶜ)
    (u v : ℂ) (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v) :
    let S := regularStarRaySet (2*k)
    factorConstant K ≤ factorConstant S ∧
      (1-(k:ℝ)^2*‖exteriorForwardCoeff F (2*k-1)‖^2)/(96*(k:ℝ)^2) ≤
        log (factorConstant S/factorConstant K) ∧
      (factorConstant K = factorConstant S ↔
        ∃ b : ℂ, ‖b‖ = 1 ∧ K = (fun z : ℂ => b*z) '' S) := by
  let G := evenExteriorPowerQuotient F k
  let Gs := evenExteriorPowerQuotient (oddStarPerturbation (2*k) 0) k
  have hG := evenExteriorPowerQuotient_actual_centered F K k hk hF hK hIm
  have hgeom := evenExteriorPowerQuotient_actual_geometry F K k hk hF hK hIm
  have hO : exteriorOmitted G = (fun z : ℂ => z^k) '' K := by
    change (G '' exteriorDisk)ᶜ = _
    rw [hgeom.2.1,compl_compl]
  have hc : IsConnected (exteriorOmitted G) := by
    rw [hO]
    exact hconn.image _ (show Continuous (fun z : ℂ => z^k) by fun_prop).continuousOn
  obtain ⟨hFs,hSIm,hS⟩ := regularEvenStar_omitted_and_invariant k hk
  have hGs : CenteredExteriorUnivalent Gs :=
    evenExteriorPowerQuotient_actual_centered _ _ k hk hFs hS hSIm
  have he := exteriorGreenCoordinate_congr_exterior Gs (slitMap 1) hGs
    (slitMap_centeredExteriorUnivalent 1 (by simp)) (regularEvenStar_powerQuotient_eqOn_slit k hk)
  apply evenStar_factorConstant_of_green_comparison F K k hk hF hK hIm u v hu hv huv
  intro r hr
  change circleAverage (exteriorGreenCoordinate G) 0 r ≤ circleAverage (exteriorGreenCoordinate Gs) 0 r
  rw [he]
  exact oddExteriorGreen_circleAverage_le_slitMap_one G hG hc hgeom.2.2 r hr

end SpringerLean
