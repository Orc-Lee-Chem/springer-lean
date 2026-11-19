import SpringerLean.Round1971PolynomialCentroid
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Polynomial Set

namespace SpringerLean

/-- Radius that converts the original positive lemniscate threshold to
unit level after division by the transformed leading coefficient. -/
noncomputable def polynomialLemniscateRadius
    (P : ℂ[X]) (t : ℝ) : ℝ :=
  (t / ‖P.leadingCoeff‖) ^ ((P.natDegree : ℝ)⁻¹)

theorem polynomialLemniscateRadius_pos_and_norm
    (P : ℂ[X]) (hP : 0 < P.natDegree)
    (t : ℝ) (ht : 0 < t) :
    0 < polynomialLemniscateRadius P t ∧
      ‖P.leadingCoeff *
        ((polynomialLemniscateRadius P t : ℝ) : ℂ) ^ P.natDegree‖ = t := by
  have hPzero : P ≠ 0 := by
    intro hzero
    simp [hzero] at hP
  have ha : 0 < ‖P.leadingCoeff‖ :=
    norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hPzero)
  have hbase : 0 < t / ‖P.leadingCoeff‖ := div_pos ht ha
  have hn : P.natDegree ≠ 0 := Nat.ne_of_gt hP
  have hr : 0 < polynomialLemniscateRadius P t := by
    unfold polynomialLemniscateRadius
    exact Real.rpow_pos_of_pos hbase _
  refine ⟨hr, ?_⟩
  have hpow : (polynomialLemniscateRadius P t) ^ P.natDegree =
      t / ‖P.leadingCoeff‖ := by
    unfold polynomialLemniscateRadius
    exact Real.rpow_inv_natCast_pow hbase.le hn
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr, hpow]
  field_simp

/-- General polynomial normalization used by Proposition 9.2. The
unit lemniscate is connected, the normalized polynomial is monic and
centered, and its degree is unchanged. This theorem starts from the
original arbitrary polynomial and its original positive threshold. -/
theorem polynomialLemniscate_normalized_centered_connected
    (P : ℂ[X]) (hP : 0 < P.natDegree)
    (t : ℝ) (ht : 0 < t)
    (hK : IsConnected {w : ℂ | ‖P.eval w‖ ≤ t}) :
    let r := polynomialLemniscateRadius P t
    let Q := polynomialAffineMonic P (polynomialZeroCentroid P) r
    0 < r ∧ Q.Monic ∧ Q.natDegree = P.natDegree ∧
      Q.roots.sum = 0 ∧
      IsConnected {z : ℂ | ‖Q.eval z‖ ≤ 1} := by
  dsimp
  obtain ⟨hr, hnorm⟩ := polynomialLemniscateRadius_pos_and_norm P hP t ht
  have hK' : IsConnected
      {w : ℂ | ‖P.eval w‖ ≤
        ‖P.leadingCoeff *
          ((polynomialLemniscateRadius P t : ℝ) : ℂ) ^ P.natDegree‖} := by
    simpa only [hnorm] using hK
  exact ⟨hr,
    polynomialAffineMonic_monic P hP _ _ hr.ne',
    polynomialAffineMonic_natDegree P _ _ hr.ne',
    polynomialAffineMonic_roots_sum_eq_zero P hP _ hr.ne',
    polynomialAffineMonic_unit_lemniscate_connected P hP _ _ hr.ne' hK'⟩

end SpringerLean

#print axioms SpringerLean.polynomialLemniscateRadius_pos_and_norm
#print axioms SpringerLean.polynomialLemniscate_normalized_centered_connected
