import SpringerLean.Round1797ActualPhaseParameters
import SpringerLean.Round1813UntruncatedScalarBudget

namespace SpringerLean
set_option maxHeartbeats 700000

/-- Exact scalar identities for the fixed paper parameter of an
actual localized endpoint, including both sides of the cutoff. -/
theorem endpointPhaseParameter_scalar_relations
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (hd : 0 < 2-‖P‖)
    (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20) :
    let m := ((2*k-2 : ℕ) : ℝ)
    let D := m*(2-‖P‖)
    let L := Real.log (2/(2-‖P‖))
    9 < L ∧ 0 < D ∧ 2*m=D*Real.exp L ∧
      (endpointPhaseParameter k P=m/5 ∨ endpointPhaseParameter k P*D*L=9) := by
  let d := 2-‖P‖
  let m := ((2*k-2 : ℕ) : ℝ)
  let L := Real.log (2/d)
  have hd0 : 0 < d := hd
  have hm : 1500 ≤ m := by dsimp [m]; exact_mod_cast (by omega : 1500 ≤ 2*k-2)
  have hm0 : 0 < m := by linarith
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1501 ≤ 2*k-1)
  have hsmall : d < 1/10000 := by
    have hh := mul_le_mul_of_nonneg_right hn hd0.le
    change ((2*k-1 : ℕ) : ℝ)*d < 3/20 at ht
    nlinarith
  have hbig : (2 : ℝ)^14 < 2/d := by
    apply (lt_div_iff₀ hd0).mpr
    norm_num
    linarith
  have hL : 9 < L := by
    have hh := Real.log_lt_log (by positivity : (0 : ℝ) < 2^14) hbig
    rw [Real.log_pow] at hh
    have hlogtwo := Real.log_two_gt_d9
    dsimp [L]
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hD : 0 < m*d := mul_pos hm0 hd0
  have hexp : 2*m=(m*d)*Real.exp L := by
    dsimp [L]
    rw [Real.exp_log (div_pos (by norm_num) hd0)]
    field_simp
    <;> ring
  have hY : 0 < endpointPhaseY k P := by
    unfold endpointPhaseY
    change 0 < m*d*L/3
    positivity
  have hcase : endpointPhaseParameter k P=m/5 ∨ endpointPhaseParameter k P*(m*d)*L=9 := by
    unfold endpointPhaseParameter
    by_cases hcut : m/5 ≤ 3/endpointPhaseY k P
    · left
      exact min_eq_right hcut
    · right
      rw [min_eq_left (le_of_lt (lt_of_not_ge hcut))]
      have heq : endpointPhaseY k P=m*d*L/3 := rfl
      rw [heq]
      field_simp
      <;> ring
  exact ⟨hL,hD,hexp,hcase⟩

end SpringerLean

#print axioms SpringerLean.endpointPhaseParameter_scalar_relations
