import SpringerLean.Round773MonicChebyshevScale
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

namespace SpringerLean

/-- The inverse scaling of the monic Chebyshev sharpness family tends to
two, so its explicit zero grid approaches the arcsine grid on `[-2,2]`. -/
theorem monicChebyshevScale_tendsto_half :
    Filter.Tendsto monicChebyshevScale Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hdiv : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / n)
      Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hexp : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / n - 1)
      Filter.atTop (nhds (-1)) := by
    simpa using hdiv.sub_const 1
  have hpow := (Real.continuousAt_const_rpow
      (by norm_num : (2 : ℝ) ≠ 0) (b := (-1 : ℝ))).tendsto.comp hexp
  convert hpow using 1
  · funext n
    rfl
  · norm_num

theorem monicChebyshevScale_inv_tendsto_two :
    Filter.Tendsto (fun n : ℕ => (monicChebyshevScale n)⁻¹)
      Filter.atTop (nhds (2 : ℝ)) := by
  convert monicChebyshevScale_tendsto_half.inv₀
    (by norm_num : (1 / 2 : ℝ) ≠ 0) using 1
  norm_num

end SpringerLean

#print axioms SpringerLean.monicChebyshevScale_tendsto_half
#print axioms SpringerLean.monicChebyshevScale_inv_tendsto_two
