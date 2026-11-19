import SpringerLean.Round2027ExteriorTransitionDisk

open scoped Topology

namespace SpringerLean

/-- Analytic expression for the transition near the compactified point
at infinity, built from the actual forward and inverse germs. -/
noncomputable def exteriorTransitionLocal (F G : ℂ → ℂ) (t : ℂ) : ℂ :=
  let u := exteriorH F t
  u / (1 - u * exteriorInverseGerm G u)

theorem exteriorTransitionLocal_analyticAt
    (F G : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hG : CenteredExteriorUnivalent G) :
    AnalyticAt ℂ (exteriorTransitionLocal F G) 0 := by
  have hHF : AnalyticAt ℂ (exteriorH F) 0 :=
    exteriorH_analyticAt F hF.2.2
  have hInv : AnalyticAt ℂ
      (fun t : ℂ => exteriorInverseGerm G (exteriorH F t)) 0 := by
    have hh : AnalyticAt ℂ (exteriorInverseGerm G) (exteriorH F 0) := by
      simpa only [exteriorH_zero] using exteriorInverseGerm_analyticAt G hG
    exact hh.comp hHF
  have hDen : AnalyticAt ℂ
      (fun t : ℂ => 1 - exteriorH F t *
        exteriorInverseGerm G (exteriorH F t)) 0 := by
    fun_prop
  have hDen0 : 1 - exteriorH F 0 *
      exteriorInverseGerm G (exteriorH F 0) ≠ 0 := by simp [exteriorH_zero]
  have h := hHF.div hDen hDen0
  convert h using 1
  funext t
  rfl

theorem exteriorTransitionLocal_hasDerivAt
    (F G : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hG : CenteredExteriorUnivalent G) :
    HasDerivAt (exteriorTransitionLocal F G) 1 0 := by
  let u := exteriorH F
  let g := exteriorInverseGerm G
  have hu : HasDerivAt u 1 0 := exteriorH_hasDerivAt F hF.2.2
  have hgu : HasDerivAt (fun t => g (u t)) (deriv g 0) 0 := by
    have hg : HasDerivAt g (deriv g 0) (u 0) := by
      simpa [u, exteriorH_zero] using
        (exteriorInverseGerm_analyticAt G hG).differentiableAt.hasDerivAt
    simpa only [Function.comp_def, mul_one] using hg.comp 0 hu
  have hprod : HasDerivAt (fun t => u t * g (u t)) 0 0 := by
    convert hu.mul hgu using 1;
      simp [u, g, exteriorH_zero, exteriorInverseGerm]
  have hDen : HasDerivAt (fun t => 1 - u t * g (u t)) 0 0 := by
    convert (hasDerivAt_const (0:ℂ) (1:ℂ)).sub hprod using 1; simp
  have h := hu.div hDen (by simp [u, exteriorH_zero])
  convert h using 1
  · funext t; rfl
  · simp [u, exteriorH_zero]

theorem exteriorTransitionDisk_eq_local_of_phi
    (F G : ℂ → ℂ)
    (hImage : F '' exteriorDisk = G '' exteriorDisk)
    (t : ℂ) (ht : t ∈ Metric.ball (0:ℂ) 1)
    (hphi : exteriorPhi F t ≠ 0) :
    exteriorTransitionDisk F G t = exteriorTransitionLocal F G t := by
  by_cases ht0 : t = 0
  · simp [ht0, exteriorTransitionDisk, exteriorTransitionLocal, exteriorH_zero]
  · have htinv : t⁻¹ ∈ exteriorDisk := by
      have htnorm : ‖t‖ < 1 := by simpa using ht
      have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
      change 1 < ‖t⁻¹‖
      rw [norm_inv]
      have h := one_div_lt_one_div_of_lt htpos htnorm
      simpa [one_div] using h
    have hFimage : F t⁻¹ ∈ G '' exteriorDisk := by
      rw [← hImage]
      exact ⟨t⁻¹, htinv, rfl⟩
    have hGinv : exteriorInverse G (F t⁻¹) ∈ exteriorDisk :=
      Function.invFunOn_mem hFimage
    have hGinv0 : exteriorInverse G (F t⁻¹) ≠ 0 := by
      intro hzero
      simp [hzero, exteriorDisk] at hGinv
      norm_num at hGinv
    let v := exteriorH F t
    have hv : v = (F t⁻¹)⁻¹ := exteriorH_eq_inv_forward F ht0 hphi
    have hv0 : v ≠ 0 := by
      dsimp [v, exteriorH]
      exact div_ne_zero ht0 hphi
    have hvinv : v⁻¹ = F t⁻¹ := by rw [hv, inv_inv]
    have hGerm : exteriorInverseGerm G v =
        v⁻¹ - exteriorInverse G v⁻¹ := by
      simp [exteriorInverseGerm, hv0]
    have hF0 : F t⁻¹ ≠ 0 := by
      intro heq
      apply hv0
      rw [hv, heq, inv_zero]
    have hprod : v * F t⁻¹ = 1 := by
      rw [hv]
      exact inv_mul_cancel₀ hF0
    have hden : 1 - v * (F t⁻¹ - exteriorInverse G (F t⁻¹)) =
        v * exteriorInverse G (F t⁻¹) := by
      calc
        _ = 1 - v * F t⁻¹ + v * exteriorInverse G (F t⁻¹) := by ring
        _ = v * exteriorInverse G (F t⁻¹) := by rw [hprod]; ring
    simp only [exteriorTransitionDisk, ht0, ↓reduceIte,
      exteriorTransitionLocal]
    change (exteriorInverse G (F t⁻¹))⁻¹ =
      v / (1 - v * exteriorInverseGerm G v)
    rw [hGerm, hvinv]
    rw [hden]
    field_simp [hv0, hGinv0]

theorem exteriorTransitionDisk_eventuallyEq_local
    (F G : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hImage : F '' exteriorDisk = G '' exteriorDisk) :
    exteriorTransitionDisk F G =ᶠ[𝓝 (0:ℂ)]
      exteriorTransitionLocal F G := by
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<1),
    exteriorPhi_eventually_ne_zero F hF.2.2] with t ht hphi
  exact exteriorTransitionDisk_eq_local_of_phi F G hImage t ht hphi

theorem exteriorTransitionDisk_analyticAt_zero
    (F G : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hG : CenteredExteriorUnivalent G)
    (hImage : F '' exteriorDisk = G '' exteriorDisk) :
    AnalyticAt ℂ (exteriorTransitionDisk F G) 0 := by
  exact (exteriorTransitionLocal_analyticAt F G hF hG).congr
    (exteriorTransitionDisk_eventuallyEq_local F G hF hImage).symm

theorem exteriorTransitionDisk_hasDerivAt_zero
    (F G : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hG : CenteredExteriorUnivalent G)
    (hImage : F '' exteriorDisk = G '' exteriorDisk) :
    HasDerivAt (exteriorTransitionDisk F G) 1 0 := by
  exact (exteriorTransitionLocal_hasDerivAt F G hF hG).congr_of_eventuallyEq
    (exteriorTransitionDisk_eventuallyEq_local F G hF hImage)

end SpringerLean

#print axioms SpringerLean.exteriorTransitionDisk_eventuallyEq_local
#print axioms SpringerLean.exteriorTransitionDisk_analyticAt_zero
#print axioms SpringerLean.exteriorTransitionDisk_hasDerivAt_zero
