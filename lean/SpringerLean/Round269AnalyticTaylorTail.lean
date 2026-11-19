import SpringerLean.Round257AllOrderActualFaber

namespace SpringerLean

/-- Repeated analytic difference quotient. This gives an exact finite
Taylor remainder without changing any derivative-defined coefficient. -/
noncomputable def analyticTaylorTail (h : ℂ → ℂ) : ℕ → (ℂ → ℂ)
  | 0 => h
  | n + 1 => dslope (analyticTaylorTail h n) 0

theorem analyticTaylorTail_analyticAt
    (h : ℂ → ℂ) (hh : AnalyticAt ℂ h 0) (n : ℕ) :
    AnalyticAt ℂ (analyticTaylorTail h n) 0 := by
  induction n with
  | zero => exact hh
  | succ n ih => exact analyticAt_dslope_zero _ ih

theorem analyticTaylorTail_coeff
    (h : ℂ → ℂ) (hh : AnalyticAt ℂ h 0) (n k : ℕ) :
    actualTaylorCoeff (analyticTaylorTail h n) k = actualTaylorCoeff h (n + k) := by
  induction n generalizing k with
  | zero => simp [analyticTaylorTail]
  | succ n ih =>
      rw [analyticTaylorTail,
        actualTaylorCoeff_dslope _ (analyticTaylorTail_analyticAt h hh n), ih]
      congr 1
      omega

theorem analyticTaylorTail_value
    (h : ℂ → ℂ) (hh : AnalyticAt ℂ h 0) (n : ℕ) :
    analyticTaylorTail h n 0 = actualTaylorCoeff h n := by
  simpa [actualTaylorCoeff] using analyticTaylorTail_coeff h hh n 0

/-- Exact finite Taylor expansion with an analytic remainder, for every
order N. The global pointwise equality follows from the dslope identity. -/
theorem analyticTaylorTail_expansion
    (h : ℂ → ℂ) (hh : AnalyticAt ℂ h 0) (N : ℕ) (u : ℂ) :
    h u = (∑ j ∈ Finset.range N, actualTaylorCoeff h j * u ^ j) +
      u ^ N * analyticTaylorTail h N u := by
  induction N with
  | zero => simp [analyticTaylorTail]
  | succ N ih =>
      have htail := analytic_dslope_decomposition (analyticTaylorTail h N) u
      rw [analyticTaylorTail_value h hh N] at htail
      change analyticTaylorTail h N u = actualTaylorCoeff h N +
        u * analyticTaylorTail h (N + 1) u at htail
      calc
        h u = (∑ j ∈ Finset.range N, actualTaylorCoeff h j * u ^ j) +
            u ^ N * analyticTaylorTail h N u := ih
        _ = (∑ j ∈ Finset.range N, actualTaylorCoeff h j * u ^ j) +
            u ^ N * (actualTaylorCoeff h N +
              u * analyticTaylorTail h (N + 1) u) := by rw [htail]
        _ = _ := by rw [Finset.sum_range_succ, pow_succ]; ring

theorem actualTaylorCoeff_var_pow_mul_zero
    (h : ℂ → ℂ) (hh : AnalyticAt ℂ h 0)
    (m n : ℕ) (hnm : n < m) :
    actualTaylorCoeff (fun u => u ^ m * h u) n = 0 := by
  rw [← actualTaylorSeries_coeff,
    actualTaylorSeries_mul (fun u : ℂ => u ^ m) h (by fun_prop) hh,
    actualTaylorSeries_monomial, PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.mpr hnm]

end SpringerLean
