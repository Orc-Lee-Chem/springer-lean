import SpringerLean.Round30AuxPair

open MeasureTheory

namespace SpringerLean

/-- A 2π-periodic integrable real function can be integrated over one full
turn by pairing positive and negative angles on the upper semicircle. -/
theorem periodic_angle_integral_pair
    (f : ℝ → ℝ) (hper : Function.Periodic f (2 * Real.pi))
    (hint : IntervalIntegrable f volume (-Real.pi) Real.pi) :
    (∫ θ in (0:ℝ)..2 * Real.pi, f θ) =
      ∫ θ in (0:ℝ)..Real.pi, (f θ + f (-θ)) := by
  have hshift : (∫ θ in (-Real.pi)..Real.pi, f θ) =
      ∫ θ in (0:ℝ)..2 * Real.pi, f θ := by
    have h := hper.intervalIntegral_add_eq (-Real.pi) 0
    convert h using 1 <;> ring
  have hleft : IntervalIntegrable f volume (-Real.pi) 0 := by
    apply hint.mono_set
    simp only [Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ 0),
      Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    intro x hx
    exact ⟨hx.1, le_trans hx.2 Real.pi_pos.le⟩
  have hright : IntervalIntegrable f volume 0 Real.pi := by
    apply hint.mono_set
    simp only [Set.uIcc_of_le (by linarith [Real.pi_pos] : 0 ≤ Real.pi),
      Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  have hsplit : (∫ θ in (-Real.pi)..Real.pi, f θ) =
      (∫ θ in (-Real.pi)..0, f θ) +
      (∫ θ in (0:ℝ)..Real.pi, f θ) :=
    (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm
  have hneg : (∫ θ in (-Real.pi)..0, f θ) =
      ∫ θ in (0:ℝ)..Real.pi, f (-θ) := by
    rw [intervalIntegral.integral_comp_neg]
    simp
  have hnegint : IntervalIntegrable (fun θ : ℝ => f (-θ)) volume 0 Real.pi := by
    simpa only [neg_zero, neg_neg] using
      (IntervalIntegrable.iff_comp_neg).mp hleft.symm
  rw [← hshift, hsplit, hneg, intervalIntegral.integral_add hright hnegint]
  exact add_comm _ _

end SpringerLean
