import SpringerLean.Round661CatalanRadiusScalar
import Mathlib.Data.Nat.Choose.Sum

open Finset

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

example : Nat.choose 1501 6 = 15725566335856300 := by norm_num [Nat.choose]

theorem binomial_1501_seven_terms : (360/359 : ℝ)^1501 > 55 := by
  have h : (360/359 : ℝ) = 1/359 + 1 := by norm_num
  rw [h, add_pow]
  have hpartial : (55 : ℝ) <
      ∑ m ∈ range 7,
        (1/359 : ℝ)^m * (1 : ℝ)^(1501-m) * (Nat.choose 1501 m : ℝ) := by
    norm_num [sum_range_succ, Nat.choose]
  have hle : (∑ m ∈ range 7,
        (1/359 : ℝ)^m * (1 : ℝ)^(1501-m) * (Nat.choose 1501 m : ℝ)) ≤
      ∑ m ∈ range (1501+1),
        (1/359 : ℝ)^m * (1 : ℝ)^(1501-m) * (Nat.choose 1501 m : ℝ) := by
    apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
    intro m hm hnot
    positivity
  exact lt_of_lt_of_le hpartial hle

namespace SpringerLean

noncomputable def normalizedCatalanOddMoment (m : ℕ) : ℝ :=
  scaledCatalanMoment m / (2 * (4 : ℝ)^m)

theorem normalizedCatalanOddMoment_nonneg (m : ℕ) :
    0 ≤ normalizedCatalanOddMoment m := by
  unfold normalizedCatalanOddMoment
  exact div_nonneg (scaledCatalanMoment_nonneg m) (by positivity)

theorem normalizedCatalanOddMoment_step (m : ℕ) :
    (2*(m : ℝ)+4)*normalizedCatalanOddMoment (m+1) =
      (2*(m : ℝ)+3)*normalizedCatalanOddMoment m := by
  have hs := scaledCatalanMoment_step m
  unfold normalizedCatalanOddMoment
  rw [pow_succ]
  have hp : (4 : ℝ)^m ≠ 0 := by positivity
  field_simp [hp]
  linear_combination 2 * hs

theorem normalizedCatalanOddMoment_square_lower (m : ℕ) :
    1 ≤ 4*((m : ℝ)+1)*(normalizedCatalanOddMoment m)^2 := by
  induction m with
  | zero => norm_num [normalizedCatalanOddMoment, scaledCatalanMoment]
  | succ m ih =>
      have hrec := normalizedCatalanOddMoment_step m
      have hs :
          (2*(m : ℝ)+4)^2*(normalizedCatalanOddMoment (m+1))^2 =
            (2*(m : ℝ)+3)^2*(normalizedCatalanOddMoment m)^2 := by
        nlinarith [congrArg (fun x : ℝ => x^2) hrec]
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hnum :
          ((m : ℝ)+1)*(2*(m : ℝ)+4)^2 ≤
            ((m : ℝ)+2)*(2*(m : ℝ)+3)^2 := by
        nlinarith
      have hA := mul_le_mul_of_nonneg_right hnum
        (sq_nonneg (normalizedCatalanOddMoment m))
      have hB := mul_le_mul_of_nonneg_left ih
        (sq_nonneg (2*(m : ℝ)+4))
      have hp : 0 < (2*(m : ℝ)+4)^2 := by positivity
      have ht :
          (2*(m : ℝ)+4)^2 * 1 ≤
            (2*(m : ℝ)+4)^2 *
              (4*((m : ℝ)+2)*(normalizedCatalanOddMoment (m+1))^2) := by
        nlinarith [hA, hB, hs]
      have htarget := (mul_le_mul_iff_of_pos_left hp).mp ht
      simpa only [Nat.cast_succ, add_assoc, one_add_one_eq_two,
        mul_one] using htarget

theorem normalizedCatalanOddMoment_base_750 :
    (359/360 : ℝ)^1501 < normalizedCatalanOddMoment 750 := by
  have hprod : (359/360 : ℝ)^1501 * (360/359 : ℝ)^1501 = 1 := by
    rw [← mul_pow]
    norm_num
  have ha : 0 < (359/360 : ℝ)^1501 := by positivity
  have hsmall : (359/360 : ℝ)^1501 < 1/55 := by
    have hh := mul_lt_mul_of_pos_left binomial_1501_seven_terms ha
    rw [hprod] at hh
    exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 55)).2 (by simpa [mul_comm] using hh)
  have hs := normalizedCatalanOddMoment_square_lower 750
  have hd0 := normalizedCatalanOddMoment_nonneg 750
  have hlarge : (1/55 : ℝ) < normalizedCatalanOddMoment 750 := by
    by_contra hh
    have hle : normalizedCatalanOddMoment 750 ≤ (1/55 : ℝ) := le_of_not_gt hh
    have hsq : (normalizedCatalanOddMoment 750)^2 ≤ (1/55 : ℝ)^2 :=
      (sq_le_sq₀ hd0 (by norm_num)).mpr hle
    norm_num at hs hsq
    nlinarith
  exact hsmall.trans hlarge

theorem normalizedCatalanOddMoment_cutoff (m : ℕ) (hm : 750 ≤ m) :
    (359/360 : ℝ)^(2*m+1) < normalizedCatalanOddMoment m := by
  induction m, hm using Nat.le_induction with
  | base => simpa using normalizedCatalanOddMoment_base_750
  | succ m hm ih =>
      have hmR : (750 : ℝ) ≤ m := by exact_mod_cast hm
      have hden : 0 < 2*(m : ℝ)+4 := by positivity
      have hrat : (359/360 : ℝ)^2 <
          (2*(m : ℝ)+3)/(2*(m : ℝ)+4) := by
        apply (lt_div_iff₀ hden).mpr
        nlinarith
      have hrec := normalizedCatalanOddMoment_step m
      have hdf : normalizedCatalanOddMoment (m+1) =
          normalizedCatalanOddMoment m *
            ((2*(m : ℝ)+3)/(2*(m : ℝ)+4)) := by
        calc
          _ = ((2*(m : ℝ)+3)*normalizedCatalanOddMoment m) /
                (2*(m : ℝ)+4) :=
              (eq_div_iff (ne_of_gt hden)).2 (by nlinarith [hrec])
          _ = _ := by ring
      have hpow : (359/360 : ℝ)^(2*(m+1)+1) =
          (359/360 : ℝ)^(2*m+1)*(359/360 : ℝ)^2 := by
        rw [show 2*(m+1)+1=(2*m+1)+2 by omega, pow_add]
      rw [hpow, hdf]
      calc
        _ < normalizedCatalanOddMoment m * (359/360 : ℝ)^2 :=
          mul_lt_mul_of_pos_right ih (by norm_num)
        _ ≤ normalizedCatalanOddMoment m *
              ((2*(m : ℝ)+3)/(2*(m : ℝ)+4)) :=
          mul_le_mul_of_nonneg_left hrat.le (normalizedCatalanOddMoment_nonneg m)

/-- Uniform strict cutoff, normalized back to the original inverse
coefficient moment: (359/180)^(2m+1) is below (2m+1) Cat_m. -/
theorem scaledCatalanMoment_cutoff359 (m : ℕ) (hm : 750 ≤ m) :
    (359/180 : ℝ)^(2*m+1) < scaledCatalanMoment m := by
  have h := normalizedCatalanOddMoment_cutoff m hm
  unfold normalizedCatalanOddMoment at h
  have hden : (0 : ℝ) < 2*(4 : ℝ)^m := by positivity
  have hh := (lt_div_iff₀ hden).mp h
  have hpow : (2 : ℝ)^(2*m+1) = 2*(4 : ℝ)^m := by
    rw [show 2*m+1=(2*m)+1 by omega, pow_add, pow_one,
      show (4 : ℝ)=2^2 by norm_num, pow_mul]
    ring
  calc
    (359/180 : ℝ)^(2*m+1) =
        (2*(359/360 : ℝ))^(2*m+1) := by norm_num
    _ = (2*(4 : ℝ)^m)*(359/360 : ℝ)^(2*m+1) := by
      rw [mul_pow, hpow]
    _ < scaledCatalanMoment m := by simpa [mul_comm] using hh

end SpringerLean
