import SpringerLean.Round31FiniteComplementSubmean
import SpringerLean.Round30AuxAnglePair

open MeasureTheory Set Metric

namespace SpringerLean

/-- Pair the positive and negative angles of an arbitrary circle-integrable
real function about a real center. -/
theorem circleAverage_real_center_eq_angle_pair
    (f : ℂ → ℝ) (a ρ : ℝ)
    (hci : CircleIntegrable f (a : ℂ) ρ) :
    Real.circleAverage f (a : ℂ) ρ =
      (2 * Real.pi)⁻¹ *
        ∫ θ in (0 : ℝ)..Real.pi,
          (f (circleMap (a : ℂ) ρ θ) +
           f (circleMap (a : ℂ) ρ (-θ))) := by
  let q : ℝ → ℝ := fun θ => f (circleMap (a : ℂ) ρ θ)
  have hper : Function.Periodic q (2 * Real.pi) := by
    intro θ
    simp [q, periodic_circleMap (a : ℂ) ρ θ]
  have hci0 : IntervalIntegrable q volume 0 (2 * Real.pi) := hci
  have hcin : IntervalIntegrable q volume (-Real.pi) Real.pi := by
    have h := (hper.intervalIntegrable_iff
      (t₁ := -Real.pi) (t₂ := 0)).2
    convert h (by simpa only [zero_add] using hci0) using 1 <;> ring
  have hpair := periodic_angle_integral_pair q hper hcin
  rw [Real.circleAverage_def]
  change (2 * Real.pi)⁻¹ * (∫ θ in (0:ℝ)..2 * Real.pi, q θ) = _
  rw [hpair]

/-- Integrability of the paired upper and lower semicircle integrand. -/
theorem circleIntegrable_angle_pair
    (f : ℂ → ℝ) (a ρ : ℝ)
    (hci : CircleIntegrable f (a : ℂ) ρ) :
    IntervalIntegrable
      (fun θ : ℝ => f (circleMap (a : ℂ) ρ θ) +
        f (circleMap (a : ℂ) ρ (-θ)))
      volume 0 Real.pi := by
  let q : ℝ → ℝ := fun θ => f (circleMap (a : ℂ) ρ θ)
  have hper : Function.Periodic q (2 * Real.pi) := by
    intro θ
    simp [q, periodic_circleMap (a : ℂ) ρ θ]
  have hci0 : IntervalIntegrable q volume 0 (2 * Real.pi) := hci
  have hcin : IntervalIntegrable q volume (-Real.pi) Real.pi := by
    have h := (hper.intervalIntegrable_iff
      (t₁ := -Real.pi) (t₂ := 0)).2
    convert h (by simpa only [zero_add] using hci0) using 1 <;> ring
  have hleft : IntervalIntegrable q volume (-Real.pi) 0 := by
    apply hcin.mono_set
    simp only [Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ 0),
      Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    intro x hx
    exact ⟨hx.1, le_trans hx.2 Real.pi_pos.le⟩
  have hright : IntervalIntegrable q volume 0 Real.pi := by
    apply hcin.mono_set
    simp only [Set.uIcc_of_le (by linarith [Real.pi_pos] : 0 ≤ Real.pi),
      Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  have hneg : IntervalIntegrable (fun θ : ℝ => q (-θ)) volume 0 Real.pi := by
    simpa only [neg_zero, neg_neg] using
      (IntervalIntegrable.iff_comp_neg).mp hleft.symm
  exact hright.add hneg
end SpringerLean