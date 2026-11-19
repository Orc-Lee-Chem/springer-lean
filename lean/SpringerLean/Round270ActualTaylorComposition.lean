import SpringerLean.Round269AnalyticTaylorTail
import SpringerLean.Round266FiniteFormalLog

namespace SpringerLean
open PowerSeries

theorem actualTaylorCoeff_add_analytic
    (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    actualTaylorCoeff (fun u => f u + g u) n =
      actualTaylorCoeff f n + actualTaylorCoeff g n := by
  have h := congrArg (PowerSeries.coeff n) (actualTaylorSeries_add f g hf hg)
  simpa only [actualTaylorSeries_coeff, map_add] using h

/-- Derivative-defined Taylor series preserve analytic composition at a
zero inner germ. The proof uses finite analytic tails and proves every
discarded term has vanishing coefficient. -/
theorem actualTaylorSeries_comp_zero
    (f H : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0) :
    actualTaylorSeries (fun u => f (H u)) =
      (actualTaylorSeries f).subst (actualTaylorSeries H) := by
  have hHseries0 : PowerSeries.constantCoeff (actualTaylorSeries H) = 0 := by
    simp [← PowerSeries.coeff_zero_eq_constantCoeff, actualTaylorCoeff, hH0]
  ext n
  let m := n + 1
  let P : ℂ → ℂ := fun u =>
    ∑ j ∈ Finset.range m, actualTaylorCoeff f j * H u ^ j
  let R : ℂ → ℂ := fun u =>
    dslope H 0 u ^ m * analyticTaylorTail f m (H u)
  have hds : AnalyticAt ℂ (dslope H 0) 0 := analyticAt_dslope_zero H hH
  have htail : AnalyticAt ℂ (analyticTaylorTail f m) (H 0) := by
    simpa [hH0] using analyticTaylorTail_analyticAt f hf m
  have hR : AnalyticAt ℂ R 0 := by dsimp [R]; fun_prop
  have hP : AnalyticAt ℂ P 0 := by dsimp [P]; fun_prop
  have hRem : AnalyticAt ℂ (fun u => u ^ m * R u) 0 := by fun_prop
  have hHu (u : ℂ) : H u = u * dslope H 0 u := by
    simpa [hH0] using analytic_dslope_decomposition H u
  have hfun : (fun u => f (H u)) = (fun u => P u + u ^ m * R u) := by
    funext u
    have hrem : H u ^ m * analyticTaylorTail f m (H u) = u ^ m * R u := by
      nth_rewrite 1 [hHu u]
      rw [mul_pow]
      dsimp [R]
      ring
    calc
      f (H u) = P u + H u ^ m * analyticTaylorTail f m (H u) := by
        simpa [P] using analyticTaylorTail_expansion f hf m (H u)
      _ = _ := by rw [hrem]
  have hcoeff : actualTaylorCoeff (fun u => f (H u)) n = actualTaylorCoeff P n := by
    rw [hfun, actualTaylorCoeff_add_analytic P _ hP hRem,
      actualTaylorCoeff_var_pow_mul_zero R hR m n (by dsimp [m]; omega), add_zero]
  have hPseries : actualTaylorSeries P =
      ∑ j ∈ Finset.range m,
        PowerSeries.C (actualTaylorCoeff f j) * (actualTaylorSeries H) ^ j := by
    dsimp only [P]
    rw [actualTaylorSeries_finset_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [actualTaylorSeries_const_mul, actualTaylorSeries_pow H hH j]
    · intro j hj
      fun_prop
  rw [actualTaylorSeries_coeff, hcoeff, ← actualTaylorSeries_coeff, hPseries]
  simp only [map_sum, PowerSeries.coeff_C_mul]
  rw [formal_coeff_subst_finite (actualTaylorSeries f) (actualTaylorSeries H) hHseries0 n]
  simp only [actualTaylorSeries_coeff, m]

end SpringerLean
