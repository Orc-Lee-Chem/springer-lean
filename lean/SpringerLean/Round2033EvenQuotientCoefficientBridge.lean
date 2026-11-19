import SpringerLean.Round2032EvenQuotientCentered
import SpringerLean.Round270ActualTaylorComposition

open Filter
open scoped Topology

namespace SpringerLean


theorem evenExteriorPowerQuotient_phi_power_germ
    (F : ℂ → ℂ) (k : ℕ) (hk : 0 < k)
    (hcov : EvenExteriorCovariant F k) :
    (fun u : ℂ => exteriorPhi (evenExteriorPowerQuotient F k) (u^k)) =ᶠ[𝓝 (0:ℂ)]
      (fun u => (exteriorPhi F u)^k) := by
  filter_upwards [Metric.ball_mem_nhds (0:ℂ)
    (by norm_num : (0:ℝ) < 1)] with u hu
  by_cases hu0 : u = 0
  · simp [hu0, exteriorPhi_zero, ne_of_gt hk]
  · have hnorm : ‖u‖ < 1 := by simpa using hu
    have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have huInv : u⁻¹ ∈ exteriorDisk := by
      change 1 < ‖u⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ hpos).2 hnorm
    have huk0 : u^k ≠ 0 := pow_ne_zero k hu0
    have hG : evenExteriorPowerQuotient F k ((u⁻¹)^k) = (F u⁻¹)^k :=
      evenExteriorPowerQuotient_comp_pow F k hk hcov u⁻¹ huInv
    have hphi (H : ℂ → ℂ) (t : ℂ) (ht : t ≠ 0) :
        exteriorPhi H t = t * H t⁻¹ := by
      rw [exteriorPhi, exteriorForwardGerm_punctured H ht]
      field_simp [ht]
      ring
    rw [hphi _ (u^k) huk0, hphi F u hu0, ← inv_pow, hG]
    ring

theorem evenExteriorPowerQuotient_phi_coeff_relation
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ) :
    PowerSeries.coeff (2*k) ((actualTaylorSeries (exteriorPhi
        (evenExteriorPowerQuotient F k))).subst (PowerSeries.X^k)) =
      PowerSeries.coeff (2*k) ((actualTaylorSeries (exteriorPhi F))^k) := by
  let G := evenExteriorPowerQuotient F k
  have hcov := evenExteriorCovariant_actual F K k hk hF hK hImage
  have hEq := evenExteriorPowerQuotient_phi_power_germ F k hk hcov
  have hSeries : actualTaylorSeries (fun u : ℂ => exteriorPhi G (u^k)) =
      actualTaylorSeries (fun u : ℂ => (exteriorPhi F u)^k) := by
    ext n
    simpa only [actualTaylorSeries_coeff] using actualTaylorCoeff_congr hEq n
  have hComp := actualTaylorSeries_comp_zero (exteriorPhi G) (fun u : ℂ => u^k)
    (evenQuotient_exteriorPhi_analyticAt_zero F K k hk hF hK hImage)
    (by fun_prop : AnalyticAt ℂ (fun u : ℂ => u^k) 0)
    (by simp [ne_of_gt hk])
  have hPow := actualTaylorSeries_pow (exteriorPhi F)
    (exteriorPhi_analyticAt F hF.2.2) k
  rw [hComp, actualTaylorSeries_monomial, hPow] at hSeries
  exact congrArg (PowerSeries.coeff (2*k)) hSeries

theorem evenExteriorPowerQuotient_firstCoeff_eq_powerTaylorCoeff
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ) :
    exteriorForwardCoeff (evenExteriorPowerQuotient F k) 1 =
      PowerSeries.coeff (2*k) ((actualTaylorSeries (exteriorPhi F))^k) := by
  have h := evenExteriorPowerQuotient_phi_coeff_relation F K k hk hF hK hImage
  rw [PowerSeries.coeff_subst_X_pow (R := ℂ) (S := ℂ)
      (by omega : k ≠ 0)] at h
  have hdiv : ((2*k : ℕ)/k) = 2 := Nat.mul_div_cancel 2 hk
  have hcoeff := actualTaylorCoeff_exteriorPhi_succ
    (evenExteriorPowerQuotient F k)
    (evenExteriorPowerQuotient_actual_centered F K k hk hF hK hImage) 1
  simpa [hdiv, hcoeff] using h

end SpringerLean

#print axioms SpringerLean.evenExteriorPowerQuotient_firstCoeff_eq_powerTaylorCoeff
