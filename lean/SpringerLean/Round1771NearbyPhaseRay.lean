import SpringerLean.Round1770SelectedTiltedTwoPowerSavings

open scoped ComplexConjugate

namespace SpringerLean

set_option maxHeartbeats 500000

/-- Squaring the phase chooses a zero of the sine, with either sign,
without rounding an angle or enumerating the k phase rays. -/
theorem exists_nearby_unit_phase_ray
    (beta ξ : ℂ) (hbeta : ‖beta‖=1) (hξ : ‖ξ‖=1)
    {k : ℕ} (hk : 0 < k) :
    ∃ (v : ℂ) (θ : ℝ), ‖v‖=1 ∧
      v=ξ*Complex.exp ((θ : ℂ)*Complex.I) ∧
      |θ| ≤ Real.pi/(2*(k : ℝ)) ∧
      ‖v-ξ‖ ≤ Real.pi/(2*(k : ℝ)) ∧
      (beta*v^k)^2=1 := by
  let c := beta*ξ^k
  let θ : ℝ := -Complex.arg (c^2)/(2*(k : ℝ))
  let v := ξ*Complex.exp ((θ : ℂ)*Complex.I)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hc : ‖c^2‖=1 := by simp [c, norm_pow, norm_mul, hbeta, hξ]
  have he : Complex.exp ((Complex.arg (c^2) : ℂ)*Complex.I)=c^2 := by
    calc
      _ = (‖c^2‖ : ℂ)*Complex.exp ((Complex.arg (c^2) : ℂ)*Complex.I) := by
        rw [hc, Complex.ofReal_one, one_mul]
      _ = c^2 := Complex.norm_mul_exp_arg_mul_I (c^2)
  have hv : ‖v‖=1 := by
    dsimp [v]
    rw [norm_mul, hξ, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hθeq : (2*(k : ℝ))*θ = -Complex.arg (c^2) := by
    dsimp [θ]
    field_simp
  have hθ : |θ| ≤ Real.pi/(2*(k : ℝ)) := by
    dsimp [θ]
    rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2*(k : ℝ))]
    exact div_le_div_of_nonneg_right (Complex.abs_arg_le_pi _) (by positivity)
  have hdist : ‖v-ξ‖ ≤ Real.pi/(2*(k : ℝ)) := by
    have hnorm : ‖v-ξ‖=‖Complex.exp (Complex.I*(θ : ℂ))-1‖ := by
      have hh : v-ξ=ξ*(Complex.exp (Complex.I*(θ : ℂ))-1) := by
        dsimp [v]; rw [mul_comm Complex.I (θ : ℂ)]; ring
      rw [hh, norm_mul, hξ, one_mul]
    rw [hnorm]
    exact ((Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ)).trans
      (by simpa only [Real.norm_eq_abs] using hθ))
  have hexp : (Complex.exp ((θ : ℂ)*Complex.I)^k)^2=
      Complex.exp (-((Complex.arg (c^2) : ℂ)*Complex.I)) := by
    rw [← pow_mul, ← Complex.exp_nat_mul]
    congr 1
    have hh : ((2*(k : ℝ))*θ : ℂ)=(-Complex.arg (c^2) : ℝ) := by
      exact_mod_cast hθeq
    push_cast at hh ⊢
    have hhc := congrArg (fun z : ℂ => z*Complex.I) hh
    push_cast at hhc
    convert hhc using 1 <;> ring
  refine ⟨v, θ, hv, rfl, hθ, hdist, ?_⟩
  calc
    (beta*v^k)^2=c^2*(Complex.exp ((θ : ℂ)*Complex.I)^k)^2 := by
      dsimp [v, c]
      rw [mul_pow]
      ring
    _ = Complex.exp ((Complex.arg (c^2) : ℂ)*Complex.I)*
        Complex.exp (-((Complex.arg (c^2) : ℂ)*Complex.I)) := by rw [hexp, he]
    _ = 1 := by rw [← Complex.exp_add]; simp

theorem exists_nearby_unit_phase_ray_large
    (beta ξ : ℂ) (hbeta : ‖beta‖=1) (hξ : ‖ξ‖=1)
    {k : ℕ} (hk : 751 ≤ k) :
    ∃ (v : ℂ) (θ : ℝ), ‖v‖=1 ∧
      v=ξ*Complex.exp ((θ : ℂ)*Complex.I) ∧
      |θ| ≤ Real.pi/(2*(k : ℝ)) ∧ ‖v-ξ‖ ≤ 1/4 ∧ (beta*v^k)^2=1 := by
  obtain ⟨v, θ, hv, heq, hθ, hd, hphase⟩ :=
    exists_nearby_unit_phase_ray beta ξ hbeta hξ (by omega : 0 < k)
  have hk' : (751 : ℝ) ≤ k := by exact_mod_cast hk
  have hpi : Real.pi/(2*(k : ℝ)) < 1/4 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*(k : ℝ))).mpr
    linarith [Real.pi_lt_four]
  exact ⟨v, θ, hv, heq, hθ, hd.trans hpi.le, hphase⟩

end SpringerLean

#print axioms SpringerLean.exists_nearby_unit_phase_ray_large
