import SpringerLean.Round2122OddGreenFullTurn

open Set Real
open scoped ComplexConjugate

namespace SpringerLean

private theorem exterior_forward_sub_bound
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (w : ℂ) (hw : w ∈ exteriorDisk) :
    ‖F w-w‖ ≤ 3/‖w‖ := by
  let z := conj w⁻¹
  have hn : ‖z‖ = ‖w‖⁻¹ := by simp [z,norm_inv]
  have hw' : 1 < ‖w‖ := hw
  have hz : ‖z‖ < 1 := by rw [hn]; exact (inv_lt_one₀ (zero_lt_one.trans hw')).mpr hw'
  have hH := actualHarmonic_norm_le_two_norm F hF hz
  have he : F w-w = actualHarmonic F z-z := by
    rw [actualHarmonic]
    simp only [z,Complex.conj_conj,exteriorForwardGerm_punctured F (inv_ne_zero (exterior_ne_zero hw)),inv_inv]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans (by rw [hn] at hH ⊢; rw [div_eq_mul_inv]; linarith)

private theorem abs_log_sub_le_abs_sub_of_one_le (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |log a-log b| ≤ |a-b| := by
  have h (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) : log x-log y ≤ |x-y| := by
    have hx' := zero_lt_one.trans_le hx
    have hy' := zero_lt_one.trans_le hy
    rw [← Real.log_div hx'.ne' hy'.ne']
    calc
      _ ≤ x/y-1 := Real.log_le_sub_one_of_pos (div_pos hx' hy')
      _ = (x-y)/y := by rw [sub_div,div_self hy'.ne']
      _ ≤ |x-y|/y := div_le_div_of_nonneg_right (le_abs_self _) hy'.le
      _ ≤ _ := div_le_self (abs_nonneg _) hy
  rw [abs_le]
  refine ⟨?_, h a b ha hb⟩
  linarith only [h b a hb ha, abs_sub_comm a b]

/-- The Green coordinate approaches the logarithm of the physical
radius uniformly at infinity. An elementary exterior bound suffices. -/
theorem exteriorGreenCoordinate_exists_far_log_bound
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (ε : ℝ) (hε : 0 < ε) :
    ∃ R ≥ (4:ℝ), ∀ z : ℂ, R < ‖z‖ → |exteriorGreenCoordinate F z-log ‖z‖| < ε := by
  classical
  let R := max 4 (3+3/ε)
  refine ⟨R,le_max_left _ _,?_⟩
  intro z hz
  have hz4 : 4 < ‖z‖ := (le_max_left _ _).trans_lt hz
  have hm : z ∈ F '' exteriorDisk := by
    by_contra h
    have h' := exteriorOmitted_norm_le_two F hF h
    linarith
  let w := exteriorInverse F z
  have hw : w ∈ exteriorDisk := Function.invFunOn_mem hm
  have hw' : 1 < ‖w‖ := hw
  have heq : F w = z := Function.invFunOn_eq hm
  have hF := exterior_forward_sub_bound F hF w hw
  rw [heq] at hF
  have h3 : ‖z-w‖ ≤ 3 := hF.trans (div_le_self (by norm_num) hw'.le)
  have hzn : ‖z‖ ≤ ‖z-w‖+‖w‖ := by
    convert norm_add_le (z-w) w using 1 <;> ring
  have hwl : 3/ε < ‖w‖ := by
    have hh := (le_max_right _ _).trans_lt hz
    linarith only [hh,hzn,h3]
  have hεw : 3/‖w‖ < ε := (div_lt_iff₀ (zero_lt_one.trans hw')).mpr
    (by have hh := (div_lt_iff₀ hε).mp hwl; nlinarith only [hh])
  rw [exteriorGreenCoordinate,if_pos hm]
  exact ((abs_log_sub_le_abs_sub_of_one_le ‖w‖ ‖z‖ hw'.le (by linarith)).trans
    ((abs_norm_sub_norm_le w z).trans (by rwa [norm_sub_rev]))).trans_lt hεw

end SpringerLean
