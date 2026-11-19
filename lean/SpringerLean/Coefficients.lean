import SpringerLean.Germ
import Mathlib.Analysis.Analytic.Uniqueness

namespace SpringerLean

/-- Candidate power series, indexed by every Taylor degree. -/
def slitTaylorCandidate (a : ℂ) (n : ℕ) : ℂ :=
  if n % 2 = 0 then 0 else slitOddCoeff a (n / 2)

@[simp] theorem slitTaylorCandidate_even (a : ℂ) (k : ℕ) :
    slitTaylorCandidate a (2 * k) = 0 := by
  have h : (2 * k) % 2 = 0 := by omega
  simp [slitTaylorCandidate, h]

@[simp] theorem slitTaylorCandidate_odd (a : ℂ) (k : ℕ) :
    slitTaylorCandidate a (2 * k + 1) = slitOddCoeff a k := by
  have h : (2 * k + 1) % 2 ≠ 0 := by omega
  have hd : (2 * k + 1) / 2 = k := by omega
  simp [slitTaylorCandidate, hd]

theorem slitInverseGerm_hasSum_all (a t : ℂ) (ha : ‖a‖ = 1)
    (ht : ‖t‖ < 1 / 4) :
    HasSum (fun n : ℕ => slitTaylorCandidate a n * t ^ n)
      (slitInverseGerm a t) := by
  have he : HasSum (fun k : ℕ => slitTaylorCandidate a (2 * k) * t ^ (2 * k)) 0 := by
    simpa only [slitTaylorCandidate_even, zero_mul] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  have ho : HasSum (fun k : ℕ => slitTaylorCandidate a (2 * k + 1) * t ^ (2 * k + 1))
      (slitInverseGerm a t) := by
    simpa only [slitTaylorCandidate_odd] using slitInverseGerm_hasSum_odd a t ha ht
  have h := HasSum.even_add_odd (f := fun n : ℕ => slitTaylorCandidate a n * t ^ n) he ho
  simpa only [zero_add] using h

theorem slitInverseGerm_hasFPowerSeriesAt (a : ℂ) (ha : ‖a‖ = 1) :
    HasFPowerSeriesAt (slitInverseGerm a)
      (FormalMultilinearSeries.ofScalars ℂ (slitTaylorCandidate a)) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < 1 / 4 by norm_num)]
    with t ht
  have ht' : ‖t‖ < 1 / 4 := by simpa [Metric.mem_ball, dist_zero_right] using ht
  simpa [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using
    (slitInverseGerm_hasSum_all a t ha ht')

/-- The actual Taylor coefficient, defined by derivatives of the actual inverse germ. -/
noncomputable def slitTaylorCoeff (a : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n (slitInverseGerm a) 0 / (n.factorial : ℂ)

theorem slitTaylorCoeff_eq_candidate (a : ℂ) (ha : ‖a‖ = 1) (n : ℕ) :
    slitTaylorCoeff a n = slitTaylorCandidate a n := by
  have hp := (slitInverseGerm_hasFPowerSeriesAt a ha).analyticAt.hasFPowerSeriesAt
  have hq := slitInverseGerm_hasFPowerSeriesAt a ha
  have h := hp.eq_formalMultilinearSeries hq
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) h
  simpa [slitTaylorCoeff, FormalMultilinearSeries.coeff_ofScalars] using hc

theorem slitTaylorCoeff_even (a : ℂ) (ha : ‖a‖ = 1) (k : ℕ) :
    slitTaylorCoeff a (2 * k) = 0 := by
  rw [slitTaylorCoeff_eq_candidate a ha]
  exact slitTaylorCandidate_even a k

theorem slitTaylorCoeff_odd (a : ℂ) (ha : ‖a‖ = 1) (k : ℕ) :
    slitTaylorCoeff a (2 * k + 1) = a ^ (k + 1) * (catalan k : ℂ) := by
  rw [slitTaylorCoeff_eq_candidate a ha, slitTaylorCandidate_odd]
  rfl

/-- The derivative-defined coefficient agrees with the old formal Catalan series. -/
theorem slitTaylorCoeff_odd_eq_slitCorrection_coeff (a : ℂ) (ha : ‖a‖ = 1) (k : ℕ) :
    slitTaylorCoeff a (2 * k + 1) = PowerSeries.coeff k (slitCorrection a) := by
  rw [slitTaylorCoeff_eq_candidate a ha, slitTaylorCandidate_odd, slitCorrection_coeff]

/-- First two coefficients of the actual inverse correction, at t and t³. -/
theorem slitTaylorCoeff_first_two (a : ℂ) (ha : ‖a‖ = 1) :
    slitTaylorCoeff a 1 = a ∧ slitTaylorCoeff a 3 = a ^ 2 := by
  constructor
  · simpa [catalan_zero] using slitTaylorCoeff_odd a ha 0
  · simpa [catalan_one] using slitTaylorCoeff_odd a ha 1
/-- The slit family reaches the Catalan value at every odd order. -/
theorem slitTaylorCoeff_odd_norm (a : ℂ) (ha : ‖a‖ = 1) (k : ℕ) :
    ‖slitTaylorCoeff a (2 * k + 1)‖ = (catalan k : ℝ) := by
  rw [slitTaylorCoeff_odd a ha k]
  simp [norm_pow, ha]

/-- Sharpness half of Theorem 1.1 for the actual rotated slit inverse. -/
theorem slitTaylorCoeff_sharp_witness (a : ℂ) (ha : ‖a‖ = 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖slitTaylorCoeff a (2 * k - 1)‖ = (catalan (k - 1) : ℝ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hidx : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  simpa only [hidx, Nat.add_sub_cancel_right] using slitTaylorCoeff_odd_norm a ha j
end SpringerLean