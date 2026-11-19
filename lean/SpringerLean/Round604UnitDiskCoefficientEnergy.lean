import SpringerLean.Round603TwoPointReciprocalBudget
import SpringerLean.Round08Actual

open MeasureTheory Filter
open scoped Topology ComplexConjugate

namespace SpringerLean
set_option Elab.async false

/-- The coefficient-energy upper bound on the actual open disk requires no
extension across the unit circle. This is the direction of Fatou needed for
the two-point midpoint proof. -/
theorem analytic_deriv_unitDisk_energy_le
    (h : ℂ → ℂ) (hh : AnalyticOnNhd ℂ h (Metric.ball (0 : ℂ) 1))
    (hsumFull : Summable (fun j : ℕ => (j : ℝ) * ‖actualTaylorCoeff h j‖ ^ 2)) :
    IntegrableOn (fun z : ℂ => ‖deriv h (conj z)‖ ^ 2) (Metric.ball (0 : ℂ) 1) ∧
      Real.pi⁻¹ * (∫ z in Metric.ball (0 : ℂ) 1, ‖deriv h (conj z)‖ ^ 2) ≤
        ∑' j : ℕ, (j : ℝ) * ‖actualTaylorCoeff h j‖ ^ 2 := by
  let d := actualTaylorCoeff h
  let w : ℕ → ℝ := fun j => (j : ℝ) * ‖d j‖ ^ 2
  have hs : Summable (fun j : ℕ => (j + 1 : ℝ) * ‖d (j + 1)‖ ^ 2) := by
    simpa only [d, Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).mpr hsumFull)
  have hcont : ContinuousOn (fun z : ℂ => deriv h (conj z)) (Metric.ball (0 : ℂ) 1) := by
    apply hh.deriv.continuousOn.comp (by fun_prop : ContinuousOn (fun z : ℂ => conj z) _)
    intro z hz
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_conj] using hz
  have hpoint : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      HasSum (fun j : ℕ => ((j + 1 : ℂ) * d (j + 1)) * (conj z) ^ j)
        (deriv h (conj z)) := by
    intro z hz
    have hzc : conj z ∈ Metric.ball (0 : ℂ) 1 := by
      simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_conj] using hz
    have ht := Complex.hasSum_taylorSeries_on_ball hh.deriv.differentiableOn hzc
    have hc (j : ℕ) :
        (↑j.factorial : ℂ)⁻¹ * iteratedDeriv j (deriv h) 0 =
          (j + 1 : ℂ) * d (j + 1) := by
      simpa [d, actualTaylorCoeff, div_eq_mul_inv, mul_comm] using actualTaylorCoeff_deriv h j
    have hterm (j : ℕ) :
        (↑j.factorial : ℂ)⁻¹ • (conj z - 0) ^ j • iteratedDeriv j (deriv h) 0 =
          ((j + 1 : ℂ) * d (j + 1)) * (conj z) ^ j := by
      simp only [sub_zero, smul_eq_mul]
      calc
        _ = ((↑j.factorial : ℂ)⁻¹ * iteratedDeriv j (deriv h) 0) * (conj z) ^ j := by ring
        _ = _ := by rw [hc]
    simpa only [hterm] using ht
  obtain ⟨hi,hb⟩ := disk_derivative_modes_fatou d _ hcont hpoint hs
  have hshift : (∑' j : ℕ, (j + 1 : ℝ) * ‖d (j + 1)‖ ^ 2) = ∑' j : ℕ, w j := by
    simpa [w, d] using hsumFull.sum_add_tsum_nat_add 1
  exact ⟨hi, hb.trans_eq hshift⟩

theorem exteriorForwardGerm_deriv_energy_le_coeff_energy
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    Real.pi⁻¹ * (∫ z in Metric.ball (0 : ℂ) 1,
      ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2) ≤
        ∑' j : ℕ, (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2 := by
  exact (analytic_deriv_unitDisk_energy_le (exteriorForwardGerm F)
    (exteriorForwardGerm_analyticOnNhd_unitBall F hc)
    (by simpa only [actualTaylorCoeff, exteriorForwardCoeff] using
      exteriorForwardCoeff_weighted_summable F hc)).2

theorem exteriorReciprocalGerm_analyticOnNhd_unitBall
    (V : ℂ → ℂ) (hV : CenteredExteriorUnivalent V)
    (hnz : ∀ z ∈ exteriorDisk, V z ≠ 0) :
    AnalyticOnNhd ℂ (exteriorReciprocalGerm V) (Metric.ball (0 : ℂ) 1) := by
  intro u hu
  by_cases hu0 : u = 0
  · subst u
    exact exteriorReciprocalGerm_analyticAt V hV
  have hu1 : ‖u‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hue : u⁻¹ ∈ exteriorDisk := by
    change 1 < ‖u⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hu0)).mpr hu1
  have hp : 1 + u * exteriorForwardGerm V u = u * V u⁻¹ := by
    rw [exteriorForwardGerm_punctured V hu0]
    field_simp
    ring
  have hd : 1 + u * exteriorForwardGerm V u ≠ 0 := by
    rw [hp]
    exact mul_ne_zero hu0 (hnz u⁻¹ hue)
  exact analyticAt_id.div (analyticAt_const.add
    (analyticAt_id.mul (exteriorForwardGerm_analyticOnNhd_unitBall V hV u hu))) hd

end SpringerLean
