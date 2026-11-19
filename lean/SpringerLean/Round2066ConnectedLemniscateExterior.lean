import SpringerLean.Round2065PolynomialRootBiholomorphism
import SpringerLean.Round2060ZeroUpperExteriorReduction
import Mathlib.Analysis.Calculus.Deriv.Slope

open Polynomial Metric Set Filter Bornology
open scoped Topology

namespace SpringerLean

private theorem polynomial_exterior_inverse_tendsto_cobounded
    (Q : ℂ[X]) (hn : 0 < Q.natDegree) (F : ℂ → ℂ)
    (hId : ∀ w ∈ exteriorDisk, Q.eval (F w) = w^Q.natDegree) (b : ℂ) :
    Tendsto (fun w => F w-b) (cobounded ℂ) (cobounded ℂ) := by
  apply tendsto_norm_atTop_iff_cobounded.mp
  apply Filter.tendsto_atTop.mpr
  intro M
  obtain ⟨Cmax,hCmax⟩ := (isCompact_closedBall b M).image Q.continuous.norm |>.bddAbove
  filter_upwards [eventually_cobounded_le_norm (E := ℂ) (max 2 (Cmax+1))] with w hw
  have hw1 : w ∈ exteriorDisk := by
    change 1 < ‖w‖
    linarith [le_max_left (2:ℝ) (Cmax+1)]
  by_contra! hlt
  have hmem : F w ∈ closedBall b M := by
    simpa [mem_closedBall, dist_eq_norm] using hlt.le
  have hQbound : ‖Q.eval (F w)‖ ≤ Cmax := hCmax ⟨F w,hmem,rfl⟩
  rw [hId w hw1, norm_pow] at hQbound
  have hpow := le_self_pow₀ (show 1 < ‖w‖ from hw1).le hn.ne'
  linarith [le_max_right (2:ℝ) (Cmax+1)]

/-- Every connected monic centered polynomial unit lemniscate has
the actual centered exterior map with its normalized polynomial identity. -/
theorem connectedLemniscateExteriorExistence_proved :
    ConnectedLemniscateExteriorExistence := by
  intro Q hQ hn hsum hconn
  obtain ⟨b,hb,H,hH0,hH,hD,hB,hpow⟩ :=
    connectedPolynomial_analytic_root_coordinate Q hQ hn hsum hconn
  let B (z : ℂ) := (z-b)*H ((z-b)⁻¹)
  obtain ⟨F,hF,hFinj,hId,hright,_⟩ := polynomial_exterior_root_biholomorphic Q hn B hB hpow
  refine ⟨F, ⟨hF.differentiableOn,hFinj,?_⟩, hId⟩
  have hU : Tendsto (fun w => (F w-b)⁻¹) (cobounded ℂ) (𝓝[≠] (0:ℂ)) :=
    tendsto_inv₀_cobounded'.comp (polynomial_exterior_inverse_tendsto_cobounded Q hn F hId b)
  have hNear : Tendsto (fun t : ℂ => (F t⁻¹-b)⁻¹)
      (𝓝[≠] (0:ℂ)) (𝓝[≠] (0:ℂ)) :=
    hU.comp tendsto_inv₀_nhdsNE_zero
  let c (t : ℂ) := (F t⁻¹-b)⁻¹
  have hslope : Tendsto (fun u : ℂ => u⁻¹ * (H u - 1))
      (𝓝[≠] (0:ℂ)) (𝓝 b) := by
    simpa only [zero_add, hH0, smul_eq_mul] using hD.tendsto_slope_zero
  have hlimit : Tendsto (exteriorForwardGerm F) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
    have h': Tendsto (fun t : ℂ => b - (c t)⁻¹ * (H (c t)-1))
        (𝓝[≠] (0:ℂ)) (𝓝 0) := by
      simpa only [sub_self, c, Function.comp_def] using (hslope.comp hNear).const_sub b
    apply h'.congr'
    have hball : ball (0:ℂ) 1 ∈ 𝓝[≠] (0:ℂ) :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (by norm_num))
    filter_upwards [hball,self_mem_nhdsWithin] with t ht ht0
    have htn : ‖t‖ < 1 := by simpa using ht
    have htInv : t⁻¹ ∈ exteriorDisk := by
      change 1 < ‖t⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.mpr ht0)).mpr htn
    have hBz : (F t⁻¹-b)*H (c t) = t⁻¹ := hright t⁻¹ htInv
    calc
      _ = F t⁻¹ - ((F t⁻¹-b)*H (c t)) := by
        dsimp [c]
        rw [inv_inv]
        ring
      _ = _ := by rw [hBz, exteriorForwardGerm_punctured F ht0]
  have hcont : ContinuousAt (exteriorForwardGerm F) 0 := by
    exact continuousAt_iff_punctured_nhds.mpr
      (by simpa only [exteriorForwardGerm_zero] using hlimit)
  have hdiff : ∀ᶠ t in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ (exteriorForwardGerm F) t := by
    have hball : ball (0:ℂ) 1 ∈ 𝓝[≠] (0:ℂ) :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (by norm_num))
    filter_upwards [hball,self_mem_nhdsWithin] with t ht ht0
    have htn : ‖t‖ < 1 := by simpa using ht
    have htInv : t⁻¹ ∈ exteriorDisk := by
      change 1 < ‖t⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.mpr ht0)).mpr htn
    have hInv : AnalyticAt ℂ (fun u : ℂ => u⁻¹) t := analyticAt_inv ht0
    have han : AnalyticAt ℂ (fun u : ℂ => F u⁻¹ - u⁻¹) t :=
      (AnalyticAt.comp (f := fun u : ℂ => u⁻¹) (hF t⁻¹ htInv) hInv).sub hInv
    apply (han.congr ?_).differentiableAt
    filter_upwards [isOpen_compl_singleton.mem_nhds
      (show t ∈ ({0} : Set ℂ)ᶜ from ht0)] with u hu
    exact (exteriorForwardGerm_punctured F hu).symm
  exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff hcont

end SpringerLean
