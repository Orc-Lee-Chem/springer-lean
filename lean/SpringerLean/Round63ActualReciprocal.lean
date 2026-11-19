import SpringerLean.Round62SchoberFinite

open scoped Topology

namespace SpringerLean

/-- Reciprocal coordinate of the actual inverse, extended analytically across zero. -/
noncomputable def schoberActualReciprocalGerm (F : ℂ → ℂ) (t : ℂ) : ℂ :=
  t / (1 - t * exteriorInverseGerm F t)

theorem schoberActualReciprocalGerm_analyticAt
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    AnalyticAt ℂ (schoberActualReciprocalGerm F) 0 := by
  have hB := exteriorInverseGerm_analyticAt F hc
  have hD : AnalyticAt ℂ (fun t : ℂ =>
      1 - t * exteriorInverseGerm F t) 0 := by
    fun_prop
  have hD0 : (1 - (0 : ℂ) * exteriorInverseGerm F 0) ≠ 0 := by norm_num
  change AnalyticAt ℂ (fun t : ℂ => t / (1 - t * exteriorInverseGerm F t)) 0
  fun_prop

theorem schoberActualReciprocalGerm_eq_actualInverse
    (F : ℂ → ℂ) {t : ℂ} (ht : t ≠ 0)
    (hD : 1 - t * exteriorInverseGerm F t ≠ 0) :
    schoberActualReciprocalGerm F t =
      (exteriorInverse F t⁻¹)⁻¹ := by
  have hB : exteriorInverseGerm F t =
      t⁻¹ - exteriorInverse F t⁻¹ := by
    simp [exteriorInverseGerm, ht]
  have hD' : t * exteriorInverse F t⁻¹ ≠ 0 := by
    simpa [hB, ht, mul_sub] using hD
  have hG : exteriorInverse F t⁻¹ ≠ 0 := by
    exact (mul_ne_zero_iff.mp hD').2
  rw [schoberActualReciprocalGerm, hB]
  field_simp [ht, hG]
  ring


private theorem schoberTaylorSeries_var_mul (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    actualTaylorSeries (fun t : ℂ => t * f t) =
      PowerSeries.X * actualTaylorSeries f := by
  ext n
  cases n with
  | zero =>
      simp [actualTaylorCoeff]
  | succ k =>
      simpa only [actualTaylorSeries_coeff, PowerSeries.coeff_succ_X_mul] using
        actualTaylorCoeff_var_mul_succ f hf k

private theorem schoberTaylorSeries_one :
    actualTaylorSeries (fun _ : ℂ => (1 : ℂ)) = 1 := by
  ext n
  cases n with
  | zero => simp [actualTaylorCoeff]
  | succ k =>
      simp [actualTaylorCoeff, iteratedDeriv_const]

private theorem schoberTaylorSeries_denominator
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorSeries (fun t : ℂ => 1 - t * exteriorInverseGerm F t) =
      1 - PowerSeries.X * schoberActualInverseSeries F := by
  ext n
  cases n with
  | zero => simp [actualTaylorCoeff, schoberActualInverseSeries]
  | succ k =>
      have hv := actualTaylorCoeff_var_mul_succ
        (exteriorInverseGerm F) (exteriorInverseGerm_analyticAt F hc) k
      have hl : actualTaylorCoeff
          (fun t : ℂ => 1 - t * exteriorInverseGerm F t) (k + 1) =
          -actualTaylorCoeff (fun t : ℂ => t * exteriorInverseGerm F t) (k + 1) := by
        simp only [actualTaylorCoeff, iteratedDeriv_const_sub (Nat.zero_lt_succ k),
          iteratedDeriv_neg]
        ring
      have hr : PowerSeries.coeff (k + 1)
          (1 - PowerSeries.X * schoberActualInverseSeries F) =
          -actualTaylorCoeff (exteriorInverseGerm F) k := by
        simp [schoberActualInverseSeries, PowerSeries.coeff_succ_X_mul]
      simp only [actualTaylorSeries_coeff]
      rw [hl, hr, hv]

/-- The reciprocal coordinate of the actual analytic inverse has precisely the
formal reciprocal series built from its independently read inverse coefficients. -/
theorem schoberActualReciprocalGerm_taylorSeries
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorSeries (schoberActualReciprocalGerm F) =
      schoberReciprocalSeries (schoberActualInverseSeries F) := by
  let D : ℂ → ℂ := fun t => 1 - t * exteriorInverseGerm F t
  let R : ℂ → ℂ := fun t => (D t)⁻¹
  let S : PowerSeries ℂ := 1 - PowerSeries.X * schoberActualInverseSeries F
  have hD : AnalyticAt ℂ D 0 := by
    have hB := exteriorInverseGerm_analyticAt F hc
    dsimp [D]
    fun_prop
  have hD0 : D 0 ≠ 0 := by norm_num [D]
  have hR : AnalyticAt ℂ R 0 := by
    exact hD.inv hD0
  have hnear : ∀ᶠ t : ℂ in 𝓝 0, D t ≠ 0 :=
    hD.continuousAt.eventually_ne hD0
  have heq : (fun t => D t * R t) =ᶠ[𝓝 (0 : ℂ)] (fun _ => (1 : ℂ)) := by
    filter_upwards [hnear] with t ht
    simp [R, ht]
  have hS : actualTaylorSeries D = S := by
    simpa only [D, S] using schoberTaylorSeries_denominator F hc
  have hprod : S * actualTaylorSeries R = 1 := by
    rw [← hS, ← actualTaylorSeries_mul D R hD hR]
    rw [← schoberTaylorSeries_one]
    ext n
    simp only [actualTaylorSeries_coeff]
    exact actualTaylorCoeff_congr heq n
  have hS0 : PowerSeries.constantCoeff S ≠ 0 := by
    simp [S]
  have hRseries : actualTaylorSeries R = S⁻¹ := by
    calc
      actualTaylorSeries R = 1 * actualTaylorSeries R := by ring
      _ = (S⁻¹ * S) * actualTaylorSeries R := by
        rw [PowerSeries.inv_mul_cancel S hS0]
      _ = S⁻¹ := by rw [mul_assoc, hprod, mul_one]
  have hfun : schoberActualReciprocalGerm F = (fun t => t * R t) := by
    funext t
    simp [schoberActualReciprocalGerm, D, R, div_eq_mul_inv]
  rw [hfun, schoberTaylorSeries_var_mul R hR, hRseries]
  rfl

/-- The finite Schober functional is the third Taylor coefficient of the
actual analytic reciprocal coordinate raised to the requested power. -/
theorem schoberActualFiniteL_eq_actualTaylorCoeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (j : ℕ) :
    schoberFiniteL (schoberActualInverseSeries F) j =
      actualTaylorCoeff (fun t => (schoberActualReciprocalGerm F t) ^ j) 3 := by
  rw [← actualTaylorSeries_coeff,
    actualTaylorSeries_pow (schoberActualReciprocalGerm F)
      (schoberActualReciprocalGerm_analyticAt F hc) j,
    schoberActualReciprocalGerm_taylorSeries F hc]
  rfl

/-- Near infinity this analytic extension evaluates the actual inverse branch. -/
theorem schoberActualReciprocalGerm_eventually_actualInverse
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∀ᶠ t : ℂ in 𝓝 (0 : ℂ), t ≠ 0 →
      schoberActualReciprocalGerm F t = (exteriorInverse F t⁻¹)⁻¹ := by
  have hD : ContinuousAt
      (fun t : ℂ => 1 - t * exteriorInverseGerm F t) 0 := by
    have hB := (exteriorInverseGerm_analyticAt F hc).continuousAt
    fun_prop
  have hD0 : (1 - (0 : ℂ) * exteriorInverseGerm F 0) ≠ 0 := by norm_num
  filter_upwards [hD.eventually_ne hD0] with t htD ht
  exact schoberActualReciprocalGerm_eq_actualInverse F ht htD
end SpringerLean