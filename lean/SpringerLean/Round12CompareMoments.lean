import SpringerLean.DiskMoments
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

open MeasureTheory
open scoped ComplexConjugate

namespace SpringerLean


/-- The comparison projection `2 Re z` is the real part of `z + conj z`. -/
theorem comparisonProjection_eq_add_conj (z : ℂ) :
    ((2 * z.re : ℝ) : ℂ) = z + conj z := by
  apply Complex.ext <;> simp; ring

/-- The normalized comparison law has total mass one. -/
theorem comparisonDisk_mass :
    (Real.pi : ℂ)⁻¹ *
      (∫ _z in Metric.ball (0 : ℂ) 1, (1 : ℂ) ∂volume) = 1 := by
  simpa using unitDisk_monomial_integral 0 0

/-- Every even moment of the actual disk comparison variable is a Catalan
number; this calculation is independent of the unproved convex-order step. -/
theorem comparisonDisk_evenMoment (k : ℕ) :
    (Real.pi : ℂ)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        (((2 * z.re : ℝ) : ℂ) ^ (2 * k)) ∂volume) =
      (catalan k : ℂ) := by
  let D : Set ℂ := Metric.ball (0 : ℂ) 1
  have hterm (m : ℕ) : IntegrableOn
      (fun z : ℂ => z ^ m * conj z ^ (2 * k - m) *
        (Nat.choose (2 * k) m : ℂ)) D := by
    have hcont : Continuous (fun z : ℂ =>
        z ^ m * conj z ^ (2 * k - m) * (Nat.choose (2 * k) m : ℂ)) := by
      fun_prop
    exact (hcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) 1)).mono_set
      Metric.ball_subset_closedBall
  simp_rw [comparisonProjection_eq_add_conj, add_pow]
  rw [integral_finsetSum (Finset.range (2 * k + 1)) (fun m _ => hterm m),
    Finset.mul_sum]
  simp_rw [integral_mul_const]
  have hdiag (m : ℕ) (hm : m ∈ Finset.range (2 * k + 1)) :
      (m = 2 * k - m) ↔ m = k := by
    simp only [Finset.mem_range] at hm
    omega
  have hreduce :
      (∑ m ∈ Finset.range (2 * k + 1),
        ((Real.pi : ℂ)⁻¹ *
          (∫ z in D, z ^ m * conj z ^ (2 * k - m) ∂volume)) *
          (Nat.choose (2 * k) m : ℂ)) =
        (Nat.choose (2 * k) k : ℂ) / (k + 1) := by
    simp_rw [show D = Metric.ball (0 : ℂ) 1 from rfl,
      unitDisk_monomial_integral]
    have hs :
        (∑ m ∈ Finset.range (2 * k + 1),
          (if m = 2 * k - m then ((m : ℂ) + 1)⁻¹ else 0) *
            (Nat.choose (2 * k) m : ℂ)) =
        (∑ m ∈ Finset.range (2 * k + 1),
          (if m = k then ((m : ℂ) + 1)⁻¹ else 0) *
            (Nat.choose (2 * k) m : ℂ)) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [hdiag m hm]
    rw [hs]
    simp [Finset.sum_ite_eq', div_eq_mul_inv, mul_comm]
    omega
  have hcat : (Nat.choose (2 * k) k : ℂ) / (k + 1) =
      (catalan k : ℂ) := by
    have h := succ_mul_catalan_eq_centralBinom k
    rw [Nat.centralBinom] at h
    have hc : ((k + 1 : ℕ) : ℂ) * (catalan k : ℂ) =
        (Nat.choose (2 * k) k : ℂ) := by exact_mod_cast h
    have hn : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : k + 1 ≠ 0)
    simp only [Nat.cast_add, Nat.cast_one] at hc hn
    apply (div_eq_iff hn).2
    simpa [mul_comm] using hc.symm
  simpa [D, mul_assoc] using hreduce.trans hcat

/-- The real-valued absolute moment for the comparison projection; the
absolute value disappears because the requested exponent is even. -/
theorem comparisonDisk_absoluteMoment (k : ℕ) :
    (Real.pi)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        |2 * z.re| ^ (2 * k) ∂volume) =
      (catalan k : ℝ) := by
  have hpoint (z : ℂ) : |2 * z.re| ^ (2 * k) =
      (2 * z.re) ^ (2 * k) := by
    simp only [pow_mul, sq_abs]
  simp_rw [hpoint]
  apply Complex.ofReal_injective
  push_cast
  rw [← integral_complex_ofReal]
  simpa only [Complex.ofReal_pow] using comparisonDisk_evenMoment k

/-- The exponent and index used in Lemma `br:proj`. -/
theorem comparisonDisk_absoluteMoment_original (k : ℕ) (hk : 1 ≤ k) :
    (Real.pi)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        |2 * z.re| ^ (2 * k - 2) ∂volume) =
      (catalan (k - 1) : ℝ) := by
  have hexp : 2 * k - 2 = 2 * (k - 1) := by omega
  simpa only [hexp] using comparisonDisk_absoluteMoment (k - 1)

theorem comparisonDisk_secondMoment :
    (Real.pi)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        |2 * z.re| ^ 2 ∂volume) = 1 := by
  simpa [catalan_one] using comparisonDisk_absoluteMoment 1

end SpringerLean
