import SpringerLean.Round1769ActualTwoPowerRetention
import SpringerLean.Round12CompareMoments
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory Metric Set

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 400000

theorem unitDisk_integral_comp_neg (f : ℂ → ℝ) :
    (∫ z in ball (0 : ℂ) 1, f (-z))=∫ z in ball (0 : ℂ) 1, f z := by
  have hpoint : (fun z : ℂ => (ball (0 : ℂ) 1).indicator (fun z => f (-z)) z)=
      (fun z => (ball (0 : ℂ) 1).indicator f (-z)) := by
    funext z
    by_cases hz : z ∈ ball (0 : ℂ) 1
    · have hz' : -z ∈ ball (0 : ℂ) 1 := by simpa using hz
      simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hz']
    · have hz' : -z ∉ ball (0 : ℂ) 1 := by simpa using hz
      simp only [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']
  rw [← integral_indicator measurableSet_ball, hpoint,
    integral_neg_eq_self, integral_indicator measurableSet_ball]

def comparisonPositiveDiskMoment (m : ℕ) : ℝ :=
  Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, (max z.re 0)^m)

/-- A strictly positive even power splits equally between the two
disk half-planes. The zeroth power is intentionally excluded. -/
theorem comparisonDisk_positivePart_evenMoment {k : ℕ} (hk : 2 ≤ k) :
    2*Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, (max (2*z.re) 0)^(2*k-2))=
      (catalan (k-1) : ℝ) := by
  let m := 2*k-2
  have hm : m ≠ 0 := by dsimp [m]; omega
  have hi := comparisonDisk_test_integrableOn (fun x : ℝ => (max x 0)^m) (by fun_prop)
  have hj := comparisonDisk_test_integrableOn (fun x : ℝ => (max (-x) 0)^m) (by fun_prop)
  have hsplit (z : ℂ) : |2*z.re|^m=(max (2*z.re) 0)^m+(max (-(2*z.re)) 0)^m := by
    by_cases hz : 0 ≤ 2*z.re
    · simp [abs_of_nonneg hz, max_eq_left hz, max_eq_right (neg_nonpos.mpr hz), hm]
    · have hz' : 2*z.re ≤ 0 := (lt_of_not_ge hz).le
      simp [abs_of_nonpos hz', max_eq_right hz', max_eq_left (neg_nonneg.mpr hz'), hm]
  have heq : (∫ z in ball (0 : ℂ) 1, (max (-(2*z.re)) 0)^m)=
      ∫ z in ball (0 : ℂ) 1, (max (2*z.re) 0)^m := by
    simpa only [Complex.neg_re, mul_neg] using
      unitDisk_integral_comp_neg (fun z => (max (2*z.re) 0)^m)
  have hcat := comparisonDisk_absoluteMoment_original k (by omega : 1 ≤ k)
  change Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, |2*z.re|^m)=(catalan (k-1) : ℝ) at hcat
  simp_rw [hsplit] at hcat
  rw [integral_add hi hj, heq] at hcat
  change 2*Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, (max (2*z.re) 0)^m)=_
  nlinarith

/-- Exact reference normalization used by the signed phase comparison:
2^(m+1) M_m = Catalan(k-1), with m=2k-2. -/
theorem comparisonPositiveDiskMoment_catalan {k : ℕ} (hk : 2 ≤ k) :
    (2 : ℝ)^(2*k-2+1)*comparisonPositiveDiskMoment (2*k-2)=
      (catalan (k-1) : ℝ) := by
  have hmax (x : ℝ) : max (2*x) 0=2*max x 0 := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx, max_eq_left (by positivity : 0 ≤ 2*x)]
    · rw [max_eq_right (le_of_lt (lt_of_not_ge hx)),
        max_eq_right (by linarith : 2*x ≤ 0), mul_zero]
  have hcat := comparisonDisk_positivePart_evenMoment hk
  simp_rw [hmax, mul_pow] at hcat
  rw [integral_const_mul] at hcat
  unfold comparisonPositiveDiskMoment
  rw [pow_succ]
  nlinarith

end
end SpringerLean

#print axioms SpringerLean.comparisonPositiveDiskMoment_catalan
