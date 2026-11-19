import SpringerLean.Round285KernelTensorExpansion
import SpringerLean.Round287TensorEnergySum
import SpringerLean.Round278EighthDiagonalArithmetic

set_option maxHeartbeats 2000000

namespace SpringerLean
open PowerSeries

/-- Schober's principal comparison for every order of the actual inverse
of the original exterior map. The actual inverse/kernel identification,
all finite matrix and tensor contractions, and the factorial energy sum
are proved internally; no Schober, area or diagonal premise remains. -/
theorem exteriorInverseCoeff_odd_norm_le_schoberDiagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (k : ℕ) :
    ‖exteriorInverseCoeff F (2 * k + 1)‖ ≤ schoberActualDiagonal F (k + 1) := by
  classical
  let n := k + 1
  let H := schoberReciprocalSeries (schoberActualInverseSeries F)
  have hH : PowerSeries.constantCoeff H = 0 := by simp [H, schoberReciprocalSeries]
  let S := formalKernelSubst H hH
  let Q := exteriorFormalGrunskyKernel F
  have hSQ : PowerSeries.constantCoeff (S Q) = 0 := by
    ext1 i
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, map_zero]
    change schoberBiCoeff i 0 (formalKernelSubst H hH Q) = 0
    rw [formalKernelSubst_biCoeff]
    simp [Q, schoberBiCoeff, PowerSeries.coeff_zero_eq_constantCoeff,
      exteriorFormalGrunskyKernel_constantCoeff]
  have hB := exteriorActual_substituted_exponential_diagonal F hc k
  change schoberBiCoeff n n ((PowerSeries.exp (PowerSeries ℂ)).subst (S Q)) =
    exteriorInverseCoeff F (2 * k + 1) at hB
  have he := congrArg (PowerSeries.coeff n)
    (finite_exp_coeff_trunc (S Q) hSQ n n le_rfl)
  simp only [map_sum, PowerSeries.algebraMap_apply, PowerSeries.coeff_C_mul,
    map_div₀, map_one, map_natCast] at he
  have hp (d : ℕ) : (S Q) ^ d = S (Q ^ d) := (map_pow S Q d).symm
  simp_rw [hp] at he
  have hrep : exteriorInverseCoeff F (2 * k + 1) =
      ∑ d ∈ Finset.range (n + 1), (1 / (d.factorial : ℂ)) *
        schoberBiCoeff n n (S (Q ^ d)) := by
    rw [← hB]
    exact he
  have hnorm : ‖exteriorInverseCoeff F (2 * k + 1)‖ ≤
      ∑ d ∈ Finset.range (n + 1), (1 / (d.factorial : ℝ)) *
        (∑ p : finiteKernelTensorIndex n d,
          ‖schoberActualA F n (finiteKernelTensorDegree n d p)‖ ^ 2 /
            finiteKernelTensorRootWeight n d p ^ 2) := by
    rw [hrep]
    calc
      _ ≤ ∑ d ∈ Finset.range (n + 1),
          ‖(1 / (d.factorial : ℂ)) * schoberBiCoeff n n (S (Q ^ d))‖ := norm_sum_le _ _
      _ = ∑ d ∈ Finset.range (n + 1),
          (1 / (d.factorial : ℝ)) * ‖schoberBiCoeff n n (S (Q ^ d))‖ := by
        apply Finset.sum_congr rfl
        intro d hd
        simp [norm_mul, norm_div]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro d hd
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact exteriorActual_kernel_power_functional_bound F hc n d
  have henergy := finiteTensor_energy_total n n le_rfl (schoberActualA F n)
    (fun m hm => schoberActualA_eq_zero_of_lt F hm)
  have hA0 : schoberActualA F n 0 = 0 := by
    simp [schoberActualA, schoberA, PowerSeries.coeff_one, n]
  have hrange : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext m
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [henergy, hrange, Finset.sum_insert (by simp), hA0, norm_zero,
    zero_pow (by omega), zero_add] at hnorm
  exact hnorm

theorem exteriorInverseCoeff_norm_le_schoberDiagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖exteriorInverseCoeff F (2 * k - 1)‖ ≤ schoberActualDiagonal F k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simpa only [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] using
    exteriorInverseCoeff_odd_norm_le_schoberDiagonal F hc m

end SpringerLean
