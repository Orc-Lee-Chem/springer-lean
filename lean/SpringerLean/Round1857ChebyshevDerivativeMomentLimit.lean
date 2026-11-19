import SpringerLean.Round1855ChebyshevMomentLimit
import SpringerLean.Round1856ChebyshevDerivativeScaling

open MeasureTheory Filter Polynomial
open scoped Topology

namespace SpringerLean

noncomputable def monicChebyshevDerivativeRadialMoment (n j : ℕ) (p : ℝ) : ℝ :=
  (((((derivative^[j]) (monicChebyshevCandidate n)).roots).map
    (fun x => |x| ^ p)).sum) / ((n : ℝ) - j)

/-- Actual monic Chebyshev derivative zeros, including the capacity
scale, satisfy the explicit empirical-moment error. -/
theorem monicChebyshevDerivativeRadialMoment_discrepancy
    (n j : ℕ) (hj : j < n) (p : ℝ) (hp : 0 < p) :
    |monicChebyshevDerivativeRadialMoment n 0 p -
        monicChebyshevDerivativeRadialMoment n j p| ≤
      2 * (2 : ℝ) ^ p * (j : ℝ) / n := by
  have hs : 0 < (monicChebyshevScale n)⁻¹ :=
    inv_pos.2 (Real.rpow_pos_of_pos (by norm_num) _)
  have hraw := chebyshev_derivative_abs_rpow_moment_discrepancy
    n j hj (monicChebyshevScale n)⁻¹ p hs.le hp
  have hconst : 2 * ((monicChebyshevScale n)⁻¹) ^ p * (j : ℝ) / n ≤
      2 * (2 : ℝ) ^ p * (j : ℝ) / n := by
    gcongr
    exact monicChebyshevScale_inv_le_two n
  simp only [monicChebyshevDerivativeRadialMoment,
    monicChebyshevCandidate_derivative_roots, Multiset.map_map, Function.comp_def,
    Function.iterate_zero, id_eq, monicChebyshevCandidate_roots,
    Nat.cast_zero, sub_zero]
  exact hraw.trans hconst

/-- For each fixed derivative order, the actual capacity-normalized
root moments converge for every real p>0.  This half of sharpness is
independent of Theorem 9.1. -/
theorem monicChebyshevDerivativeRadialMoment_tendsto
    (j : ℕ) (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n : ℕ => monicChebyshevDerivativeRadialMoment n j p)
      atTop (𝓝 (arcsineRadialMomentIntegral p)) := by
  have h0 : Tendsto (fun n : ℕ => monicChebyshevDerivativeRadialMoment n 0 p)
      atTop (𝓝 (arcsineRadialMomentIntegral p)) := by
    simpa only [monicChebyshevDerivativeRadialMoment, Function.iterate_zero,
      id_eq, Nat.cast_zero, sub_zero] using
      monicChebyshevCandidate_abs_rpow_moment_tendsto p hp
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖monicChebyshevDerivativeRadialMoment n j p -
        monicChebyshevDerivativeRadialMoment n 0 p‖ ≤
          (2 * (2 : ℝ) ^ p * (j : ℝ)) / n := by
    filter_upwards [eventually_gt_atTop j] with n hn
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact monicChebyshevDerivativeRadialMoment_discrepancy n j hn p hp
  have herr : Tendsto (fun n : ℕ => (2 * (2 : ℝ) ^ p * (j : ℝ)) / n)
      atTop (𝓝 (0 : ℝ)) := by
    convert tendsto_one_div_atTop_nhds_zero_nat.const_mul
      (2 * (2 : ℝ) ^ p * (j : ℝ)) using 1 <;> simp [div_eq_mul_inv]
  have hz := squeeze_zero_norm' hbound herr
  simpa only [sub_add_cancel, zero_add] using hz.add h0

end SpringerLean

#print axioms SpringerLean.monicChebyshevDerivativeRadialMoment_discrepancy
#print axioms SpringerLean.monicChebyshevDerivativeRadialMoment_tendsto
