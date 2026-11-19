import SpringerLean.Round2045PolynomialExteriorFibers
import SpringerLean.Round2046ExteriorJensen
import Mathlib.Analysis.Polynomial.MahlerMeasure

open Metric Set Real Polynomial Filter

namespace SpringerLean

/-- The logarithmic potential of a smooth exterior circle of a
polynomial lemniscate, at every point of the plane. -/
theorem polynomial_exterior_circle_log_potential
    (Q : ℂ[X]) (hdeg : 0 < Q.natDegree)
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hidentity : ∀ w ∈ exteriorDisk, Q.eval (F w) = w ^ Q.natDegree)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (x : ℂ) :
    circleAverage (fun z => Real.log ‖F z - x‖) 0 r⁻¹ =
      max (-Real.log r) (Real.log ‖Q.eval x‖ / (Q.natDegree : ℝ)) := by
  have hn : 0 < (Q.natDegree : ℝ) := by exact_mod_cast hdeg
  have hrInv : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  by_cases hx : x ∈ F '' exteriorDisk
  · obtain ⟨w, hw, rfl⟩ := hx
    rw [exterior_circle_log_potential_at_image F hF w hw r hr hr1,
      hidentity w hw, norm_pow, Real.log_pow]
    rw [mul_div_cancel_left₀ _ hn.ne', ← Real.log_inv]
    have hwPos : 0 < ‖w‖ := lt_trans zero_lt_one hw
    rcases le_total r⁻¹ ‖w‖ with h | h
    · rw [max_eq_right h, max_eq_right (Real.log_le_log (inv_pos.mpr hr) h)]
    · rw [max_eq_left h, max_eq_left (Real.log_le_log hwPos h)]
  · rw [exterior_circle_log_potential_of_omitted F hF x hx r hr hr1]
    rw [polynomial_exterior_image_eq Q hdeg F hF.2.1 hidentity] at hx
    have hxle : ‖Q.eval x‖ ≤ 1 := le_of_not_gt hx
    have hlog : Real.log ‖Q.eval x‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hxle
    have hdiv : Real.log ‖Q.eval x‖ / (Q.natDegree : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hlog hn.le
    have hpos : 0 ≤ -Real.log r := by
      rw [← Real.log_inv]
      exact Real.log_nonneg hrInv.le
    rw [max_eq_left (hdiv.trans hpos)]

theorem polynomial_exterior_circle_log_potential_continuous_formula
    (Q : ℂ[X]) (hdeg : 0 < Q.natDegree)
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hidentity : ∀ w ∈ exteriorDisk, Q.eval (F w) = w ^ Q.natDegree)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (x : ℂ) :
    circleAverage (fun z => Real.log ‖F z - x‖) 0 r⁻¹ =
      Real.log (max (r⁻¹ ^ Q.natDegree) ‖Q.eval x‖) / (Q.natDegree : ℝ) := by
  rw [polynomial_exterior_circle_log_potential Q hdeg F hF hidentity r hr hr1,
    ← Real.log_inv]
  have hn : 0 < (Q.natDegree : ℝ) := by exact_mod_cast hdeg
  have hrp : 0 < r⁻¹ ^ Q.natDegree := pow_pos (inv_pos.mpr hr) _
  have hden : Real.log (r⁻¹ ^ Q.natDegree) / (Q.natDegree : ℝ) =
      Real.log r⁻¹ := by
    rw [Real.log_pow, mul_div_cancel_left₀ _ hn.ne']
  rcases le_total (r⁻¹ ^ Q.natDegree) ‖Q.eval x‖ with h | h
  · have hineq : Real.log r⁻¹ ≤ Real.log ‖Q.eval x‖ / (Q.natDegree : ℝ) := by
      rw [← hden]
      exact div_le_div_of_nonneg_right (Real.log_le_log hrp h) hn.le
    rw [max_eq_right h, max_eq_right hineq]
  · have hineq : Real.log ‖Q.eval x‖ / (Q.natDegree : ℝ) ≤ Real.log r⁻¹ := by
      by_cases hx : Q.eval x = 0
      · simpa only [hx, norm_zero, Real.log_zero, zero_div] using
          Real.log_nonneg ((one_lt_inv₀ hr).mpr hr1).le
      · rw [← hden]
        exact div_le_div_of_nonneg_right (Real.log_le_log (norm_pos_iff.mpr hx) h) hn.le
    rw [max_eq_left h, max_eq_left hineq, hden]

theorem monic_polynomial_circleAverage_log_norm_eq_sum
    (Q : ℂ[X]) (hQ : Q.Monic) (s : ℝ) (hs : 0 < s) :
    circleAverage (fun z => Real.log ‖Q.eval z‖) 0 s =
      (Q.natDegree : ℝ) * Real.log s +
        (Q.roots.map (fun z : ℂ => Real.posLog (‖z‖ / s))).sum := by
  let P := Q.comp (C (s : ℂ) * X)
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hroots : P.roots = Q.roots.map (fun z : ℂ => (s : ℂ)⁻¹ * z) := by
    simpa only [P, C_0, add_zero, sub_zero, Ring.inverse_eq_inv] using
      roots_comp_C_mul_X_add_C Q (s : ℂ) (0 : ℂ) (isUnit_iff_ne_zero.mpr hsC)
  have hlead : P.leadingCoeff = (s : ℂ) ^ Q.natDegree := by
    unfold P
    rw [leadingCoeff_comp, hQ.leadingCoeff, one_mul, leadingCoeff_C_mul_X]
    rw [natDegree_C_mul_X _ hsC]
    decide
  have hlog : Real.log ‖P.leadingCoeff‖ = (Q.natDegree : ℝ) * Real.log s := by
    rw [hlead, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, Real.log_pow]
  calc
    _ = P.logMahlerMeasure := by
      rw [circleAverage_eq_circleAverage_zero_one, logMahlerMeasure_def]
      simp [P, eval_comp]
    _ = _ := by
      rw [logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots, hlog, hroots,
        Multiset.map_map]
      simp only [Function.comp_def, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs, div_eq_mul_inv, mul_comm]

end SpringerLean
