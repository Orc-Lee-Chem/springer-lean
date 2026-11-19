import SpringerLean.Round283FiniteKernelTruncation
import SpringerLean.Round284FiniteTensorProducts

namespace SpringerLean
open PowerSeries

theorem formalKernelMonomial_mul (c e : ℂ) (p q r s : ℕ) :
    formalKernelMonomial c p q * formalKernelMonomial e r s =
      formalKernelMonomial (c * e) (p + r) (q + s) := by
  simp only [formalKernelMonomial, map_mul, pow_add]
  ring

theorem exteriorTruncatedGeneralKernel_pow
    (F : ℂ → ℂ) (N d : ℕ) :
    exteriorTruncatedGeneralKernel F N ^ d =
      ∑ p : finiteKernelTensorIndex N d, ∑ q : finiteKernelTensorIndex N d,
        formalKernelMonomial
          (finiteKernelTensorPower N (exteriorGeneralUnweightedKernel F N) d p q)
          (finiteKernelTensorDegree N d p) (finiteKernelTensorDegree N d q) := by
  classical
  induction d with
  | zero =>
      letI : Unique (finiteKernelTensorIndex N 0) := inferInstanceAs (Unique PUnit)
      simp [finiteKernelTensorPower, finiteKernelTensorDegree, formalKernelMonomial]
  | succ d ih =>
      change exteriorTruncatedGeneralKernel F N ^ (d + 1) =
        ∑ p : finiteKernelTensorIndex N d × Fin N,
          ∑ q : finiteKernelTensorIndex N d × Fin N,
            formalKernelMonomial
              (finiteKernelTensorPower N (exteriorGeneralUnweightedKernel F N) d p.1 q.1 *
                exteriorGeneralUnweightedKernel F N p.2 q.2)
              (finiteKernelTensorDegree N d p.1 + (p.2.val + 1))
              (finiteKernelTensorDegree N d q.1 + (q.2.val + 1))
      rw [pow_succ, ih, Finset.sum_mul]
      simp_rw [Finset.sum_mul]
      simp only [exteriorTruncatedGeneralKernel, Finset.mul_sum,
        Fintype.sum_prod_type, formalKernelMonomial_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]

theorem formalKernelSubst_monomial_biCoeff
    (H : PowerSeries ℂ) (hH : PowerSeries.constantCoeff H = 0)
    (c : ℂ) (p q i j : ℕ) :
    schoberBiCoeff i j (formalKernelSubst H hH (formalKernelMonomial c p q)) =
      c * PowerSeries.coeff i (H ^ p) * PowerSeries.coeff j (H ^ q) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hH
  have hC : (PowerSeries.C c).subst H = PowerSeries.C c :=
    PowerSeries.subst_C c
  have hmap : formalKernelSubst H hH (formalKernelMonomial c p q) =
      PowerSeries.C (PowerSeries.C c) *
        (PowerSeries.map (PowerSeries.C : ℂ →+* PowerSeries ℂ) H) ^ q *
          PowerSeries.C (H ^ p) := by
    simp only [formalKernelMonomial, map_mul, map_pow, formalKernelSubst_C,
      formalKernelSubst_X, PowerSeries.subst_pow hs, PowerSeries.subst_X hs, hC]
  rw [hmap]
  unfold schoberBiCoeff
  rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul,
    ← map_pow, PowerSeries.coeff_map, ← map_mul, PowerSeries.coeff_C_mul]
  ring

theorem exteriorTruncatedKernel_power_functional
    (F : ℂ → ℂ) (N n d : ℕ) :
    let H := schoberReciprocalSeries (schoberActualInverseSeries F)
    let hH : PowerSeries.constantCoeff H = 0 := by simp [H, schoberReciprocalSeries]
    schoberBiCoeff n n (formalKernelSubst H hH
      (exteriorTruncatedGeneralKernel F N ^ d)) =
      ∑ p : finiteKernelTensorIndex N d, schoberActualA F n (finiteKernelTensorDegree N d p) *
        (∑ q : finiteKernelTensorIndex N d,
          finiteKernelTensorPower N (exteriorGeneralUnweightedKernel F N) d p q *
            schoberActualA F n (finiteKernelTensorDegree N d q)) := by
  classical
  dsimp only
  rw [exteriorTruncatedGeneralKernel_pow]
  simp only [map_sum, schoberBiCoeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [show PowerSeries.coeff n (PowerSeries.coeff n
      (formalKernelSubst _ _ (formalKernelMonomial _ _ _))) = _ from
        formalKernelSubst_monomial_biCoeff _ _ _ _ _ n n]
  unfold schoberActualA schoberA
  ring

theorem exteriorActual_kernel_power_functional_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (n d : ℕ) :
    let H := schoberReciprocalSeries (schoberActualInverseSeries F)
    let hH : PowerSeries.constantCoeff H = 0 := by simp [H, schoberReciprocalSeries]
    ‖schoberBiCoeff n n (formalKernelSubst H hH (exteriorFormalGrunskyKernel F ^ d))‖ ≤
      ∑ p : finiteKernelTensorIndex n d,
        ‖schoberActualA F n (finiteKernelTensorDegree n d p)‖ ^ 2 /
          finiteKernelTensorRootWeight n d p ^ 2 := by
  dsimp only
  have hH : PowerSeries.constantCoeff
      (schoberReciprocalSeries (schoberActualInverseSeries F)) = 0 := by
    simp [schoberReciprocalSeries]
  have heq := schoberLowEq_kernelSubst _ hH
    (schoberLowEq_pow (exteriorTruncatedGeneralKernel_low_eq F n) d)
    n n (by omega) (by omega)
  rw [heq, exteriorTruncatedKernel_power_functional]
  exact exteriorGeneralGrunskyTensor_functional_bound F hc n d (schoberActualA F n)

end SpringerLean
