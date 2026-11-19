import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SpringerLean
set_option Elab.async false

noncomputable def scaledCatalanMoment (m : ℕ) : ℝ :=
  (2*(m : ℝ)+1)*(catalan m : ℝ)

theorem scaledCatalanMoment_nonneg (m : ℕ) : 0 ≤ scaledCatalanMoment m := by
  dsimp only [scaledCatalanMoment]
  positivity

theorem catalan_real_step (m : ℕ) :
    ((m : ℝ)+2)*(catalan (m+1) : ℝ) =
      2*(2*(m : ℝ)+1)*(catalan m : ℝ) := by
  have h := Nat.succ_mul_centralBinom_succ m
  rw [← succ_mul_catalan_eq_centralBinom (m+1),
    ← succ_mul_catalan_eq_centralBinom m] at h
  have hr := congrArg (fun a : ℕ => (a : ℝ)) h
  push_cast at hr
  apply mul_left_cancel₀ (by positivity : (m : ℝ)+1 ≠ 0)
  calc
    _ = 2*(2*(m : ℝ)+1)*(((m : ℝ)+1)*(catalan m : ℝ)) := by
      convert hr using 1 <;> ring
    _ = _ := by ring

theorem scaledCatalanMoment_step (m : ℕ) :
    ((m : ℝ)+2)*scaledCatalanMoment (m+1) =
      2*(2*(m : ℝ)+3)*scaledCatalanMoment m := by
  have h := catalan_real_step m
  dsimp only [scaledCatalanMoment]
  push_cast
  linear_combination (2*(m : ℝ)+3)*h

theorem scaledCatalanMoment_growth (m : ℕ) (hm : 6 ≤ m) :
    (15/4 : ℝ)*scaledCatalanMoment m ≤ scaledCatalanMoment (m+1) := by
  have hrec := scaledCatalanMoment_step m
  have hmR : (6 : ℝ) ≤ m := by exact_mod_cast hm
  have hnonneg : 0 ≤ (((m : ℝ)-6)/4)*scaledCatalanMoment m :=
    mul_nonneg (by linarith) (scaledCatalanMoment_nonneg m)
  have hid : ((m : ℝ)+2)*scaledCatalanMoment (m+1)-
      ((m : ℝ)+2)*((15/4 : ℝ)*scaledCatalanMoment m) =
        (((m : ℝ)-6)/4)*scaledCatalanMoment m := by
    linear_combination hrec
  apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < (m : ℝ)+2)).mp
  linarith

theorem catalan_twenty_six_exact : catalan 26 = 18367353072152 := by
  rw [catalan_eq_centralBinom_div]
  change Nat.choose 52 26 / 27 = 18367353072152
  rw [Nat.choose_eq_factorial_div_factorial (by decide : 26 ≤ 52)]
  norm_num [Nat.factorial]

/-- A uniform analytic-radius threshold; not a finite table of orders. -/
theorem catalan_candidate_radius_scalar (m : ℕ) (hm : 26 ≤ m) :
    (237/125 : ℝ)^(2*m+1) < scaledCatalanMoment m := by
  induction m,hm using Nat.le_induction with
  | base => norm_num [scaledCatalanMoment,catalan_twenty_six_exact]
  | succ m hm ih =>
      have hg := scaledCatalanMoment_growth m (by omega)
      have hpow : (237/125 : ℝ)^(2*(m+1)+1) =
          (237/125 : ℝ)^(2*m+1)*(237/125 : ℝ)^2 := by
        rw [show 2*(m+1)+1=(2*m+1)+2 by omega,pow_add]
      rw [hpow]
      calc
        _ ≤ (237/125 : ℝ)^(2*m+1)*(15/4 : ℝ) :=
          mul_le_mul_of_nonneg_left (by norm_num)
            (pow_nonneg (by norm_num) _)
        _ < scaledCatalanMoment m*(15/4 : ℝ) :=
          mul_lt_mul_of_pos_right ih (by norm_num)
        _ = (15/4 : ℝ)*scaledCatalanMoment m := mul_comm _ _
        _ ≤ _ := hg

end SpringerLean
