import SpringerLean.Round280ActualExponentialKernel
import SpringerLean.Round267FormalLogLowCoefficients

namespace SpringerLean
open PowerSeries

theorem formalKernelSubst_biCoeff
    (H : PowerSeries ℂ) (hH : PowerSeries.constantCoeff H = 0)
    (Q : PowerSeries (PowerSeries ℂ)) (i j : ℕ) :
    schoberBiCoeff i j (formalKernelSubst H hH Q) =
      ∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (i + 1),
        schoberBiCoeff q p Q * PowerSeries.coeff i (H ^ q) *
          PowerSeries.coeff j (H ^ p) := by
  let HH := PowerSeries.map (PowerSeries.C : ℂ →+* PowerSeries ℂ) H
  have hHH : PowerSeries.constantCoeff HH = 0 := by
    change PowerSeries.C (PowerSeries.constantCoeff H) = 0
    rw [hH, map_zero]
  have hp (p : ℕ) : PowerSeries.coeff j (HH ^ p) =
      PowerSeries.C (PowerSeries.coeff j (H ^ p)) := by
    dsimp only [HH]
    rw [← map_pow, PowerSeries.coeff_map]
  change PowerSeries.coeff i (PowerSeries.coeff j
    ((PowerSeries.map (formalSubstRingHom H hH) Q).subst HH)) = _
  rw [formal_coeff_subst_finite _ HH hHH j]
  simp only [map_sum, hp, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_map, formalSubstRingHom_apply]
  apply Finset.sum_congr rfl
  intro p hp'
  rw [formal_coeff_subst_finite _ H hH i, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rfl

theorem schoberLowEq_kernelSubst
    (H : PowerSeries ℂ) (hH : PowerSeries.constantCoeff H = 0)
    {n : ℕ} {A B : PowerSeries (PowerSeries ℂ)} (hAB : schoberLowEq n A B) :
    schoberLowEq n (formalKernelSubst H hH A) (formalKernelSubst H hH B) := by
  intro i j hi hj
  rw [formalKernelSubst_biCoeff, formalKernelSubst_biCoeff]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  have hpn : p < n := by have := Finset.mem_range.mp hp; omega
  have hqn : q < n := by have := Finset.mem_range.mp hq; omega
  rw [hAB q p hqn hpn]

end SpringerLean
