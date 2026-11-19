import SpringerLean.Round274FormalExpLog
import SpringerLean.Round284FiniteTensorProducts
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.WellKnown

namespace SpringerLean
open PowerSeries

theorem formal_coeff_pow_congr_low
    {A : Type*} [CommRing A] (f g : PowerSeries A) (N : ℕ)
    (hfg : ∀ m < N, PowerSeries.coeff m f = PowerSeries.coeff m g)
    (m : ℕ) (hm : m < N) (d : ℕ) :
    PowerSeries.coeff m (f ^ d) = PowerSeries.coeff m (g ^ d) := by
  have ht : PowerSeries.trunc N f = PowerSeries.trunc N g := by
    ext k
    rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
    split_ifs with hk
    · exact hfg k hk
    · rfl
  have hp : PowerSeries.trunc N (f ^ d) = PowerSeries.trunc N (g ^ d) := by
    rw [← PowerSeries.trunc_trunc_pow f N d, ht,
      PowerSeries.trunc_trunc_pow g N d]
  have h := congrArg (fun P : Polynomial A => P.coeff m) hp
  simpa only [PowerSeries.coeff_trunc, ite_eq_left hm] using h

theorem formal_exp_coeff_congr_low
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (f g : PowerSeries A) (hf : PowerSeries.constantCoeff f = 0)
    (hg : PowerSeries.constantCoeff g = 0) (N : ℕ)
    (hfg : ∀ m < N, PowerSeries.coeff m f = PowerSeries.coeff m g)
    (m : ℕ) (hm : m < N) :
    PowerSeries.coeff m ((PowerSeries.exp A).subst f) =
      PowerSeries.coeff m ((PowerSeries.exp A).subst g) := by
  rw [formal_exp_coeff_finite f hf m, formal_exp_coeff_finite g hg m]
  apply Finset.sum_congr rfl
  intro d hd
  rw [formal_coeff_pow_congr_low f g N hfg m hm d]

noncomputable def finiteLogTruncation (N : ℕ) : PowerSeries ℝ :=
  ∑ i : Fin N, PowerSeries.C ((((i.val + 1 : ℕ) : ℝ))⁻¹) *
    PowerSeries.X ^ (i.val + 1)

theorem finiteLogTruncation_zero (N : ℕ) :
    PowerSeries.constantCoeff (finiteLogTruncation N) = 0 := by
  simp [finiteLogTruncation]

theorem finiteLogTruncation_coeff_succ (N k : ℕ) (hk : k < N) :
    PowerSeries.coeff (k + 1) (finiteLogTruncation N) =
      (((k + 1 : ℕ) : ℝ))⁻¹ := by
  classical
  let ik : Fin N := ⟨k, hk⟩
  simp only [finiteLogTruncation, map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  rw [Finset.sum_eq_single ik]
  · simp [ik]
  · intro i hi hne
    have hki : k + 1 ≠ i.val + 1 := by
      intro heq
      apply hne
      apply Fin.ext
      dsimp [ik]
      omega
    have hki' : k ≠ i.val := by omega
    simp [hki']
  · simp

theorem finiteLogTruncation_coeff_low (N m : ℕ) (hm : m ≤ N) :
    PowerSeries.coeff m (finiteLogTruncation N) =
      PowerSeries.coeff m (formalNegativeLogSeries ℝ) := by
  cases m with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff, finiteLogTruncation_zero]
  | succ k =>
      rw [finiteLogTruncation_coeff_succ N k (by omega), formalNegativeLogSeries_coeff_succ]
      simp

theorem formalNegativeLogSeries_exp_coeff_real (m : ℕ) :
    PowerSeries.coeff m ((PowerSeries.exp ℝ).subst (formalNegativeLogSeries ℝ)) = 1 := by
  rw [formalNegativeLogSeries, formal_exp_negative_log PowerSeries.X (by simp)]
  have hu : IsUnit (1 - PowerSeries.X : PowerSeries ℝ) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp)
  have heq : PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℝ) 1 =
      PowerSeries.mk (1 : ℕ → ℝ) := by
    apply hu.mul_left_cancel
    rw [PowerSeries.mul_invOfUnit _ _ (by simp), mul_comm,
      PowerSeries.mk_one_mul_one_sub_eq_one]
  rw [heq]
  rfl

theorem finiteLogTruncation_exp_coeff_low (N m : ℕ) (hm : m ≤ N) :
    PowerSeries.coeff m ((PowerSeries.exp ℝ).subst (finiteLogTruncation N)) = 1 := by
  rw [formal_exp_coeff_congr_low (finiteLogTruncation N) (formalNegativeLogSeries ℝ)
    (finiteLogTruncation_zero N) formalNegativeLogSeries_constantCoeff (N + 1)
    (fun k hk => finiteLogTruncation_coeff_low N k (by omega)) m (by omega)]
  exact formalNegativeLogSeries_exp_coeff_real m

end SpringerLean
