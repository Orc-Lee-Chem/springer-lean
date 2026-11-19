import SpringerLean.Round1457CandidateRatioScalar

open MeasureTheory

namespace SpringerLean
set_option maxHeartbeats 250000

/-- A fourth-degree polynomial minorant for the cosine on the
positive half-circle. This is the source of the `0.502/n` reserve. -/
theorem halfCosMoment_succ_refined_lower
    (n : ℕ) (hn : 1501 ≤ n) :
    (1-(251/500:ℝ)/(n:ℝ))*halfCosMoment n ≤
      halfCosMoment (n+1) := by
  let C : ℕ → ℝ := halfCosMoment
  have hnR : (1501:ℝ) ≤ n := by exact_mod_cast hn
  have hC0 : 0 ≤ C n := (EulerSine.integral_cos_pow_pos n).le
  have hpoint (θ : ℝ)
      (hθ : θ ∈ Set.Icc 0 (Real.pi/2)) :
      3*Real.cos θ^(n+2)-Real.cos θ^(n+4) ≤
        2*Real.cos θ^(n+1) := by
    have hc0 : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩
    have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hpoly : 0 ≤ Real.cos θ * (Real.cos θ-1)^2 *
        (Real.cos θ+2) := by positivity
    have hmul := mul_nonneg (pow_nonneg hc0 n) hpoly
    have hpow1 : Real.cos θ^(n+1)=Real.cos θ^n*Real.cos θ := by
      rw [pow_succ]
    have hpow2 : Real.cos θ^(n+2)=Real.cos θ^n*Real.cos θ^2 := by
      rw [show n+2=n+2 by rfl,pow_add]
    have hpow4 : Real.cos θ^(n+4)=Real.cos θ^n*Real.cos θ^4 := by
      rw [pow_add]
    rw [hpow1,hpow2,hpow4]
    nlinarith [hmul]
  have hInt (j : ℕ) : IntervalIntegrable
      (fun θ : ℝ => Real.cos θ^j) volume 0 (Real.pi/2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hraw : 3*C (n+2)-C (n+4) ≤ 2*C (n+1) := by
    have hh : (∫ θ in (0:ℝ)..Real.pi/2,
        3*Real.cos θ^(n+2)-Real.cos θ^(n+4)) ≤
        ∫ θ in (0:ℝ)..Real.pi/2,
          2*Real.cos θ^(n+1) := by
      apply intervalIntegral.integral_mono_on
        (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi/2)
      · exact ((hInt (n+2)).const_mul _).sub (hInt (n+4))
      · exact (hInt (n+1)).const_mul _
      · intro θ hθ
        exact hpoint θ hθ
    rw [intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hh
    · exact hh
    · exact (hInt (n+2)).const_mul _
    · exact hInt (n+4)
  have hrec1 := halfCosMoment_succ_succ n
  have hrec2 := halfCosMoment_succ_succ (n+2)
  change C (n+2) = ((n+1:ℕ):ℝ)/((n+2:ℕ):ℝ)*C n at hrec1
  change C (n+4) = ((n+3:ℕ):ℝ)/((n+4:ℕ):ℝ)*C (n+2) at hrec2
  have hcast1 : ((n+1:ℕ):ℝ)=(n:ℝ)+1 := by push_cast; ring
  have hcast2 : ((n+2:ℕ):ℝ)=(n:ℝ)+2 := by push_cast; ring
  have hcast3 : ((n+3:ℕ):ℝ)=(n:ℝ)+3 := by push_cast; ring
  have hcast4 : ((n+4:ℕ):ℝ)=(n:ℝ)+4 := by push_cast; ring
  rw [hcast1,hcast2] at hrec1
  rw [hcast3,hcast4] at hrec2
  have hrec : C (n+4) =
      (((n:ℝ)+3)/((n:ℝ)+4))*
        (((n:ℝ)+1)/((n:ℝ)+2))*C n := by
    rw [hrec2,hrec1]
    ring
  rw [hrec1,hrec] at hraw
  have hscalar := refinedCandidate_cos_ratio_scalar hnR
  have hpos : 0 < (n:ℝ)+2 := by linarith
  have hpos4 : 0 < (n:ℝ)+4 := by linarith
  have hformula :
      3*(((n:ℝ)+1)/((n:ℝ)+2)*C n) -
        (((n:ℝ)+3)/((n:ℝ)+4))*
          (((n:ℝ)+1)/((n:ℝ)+2))*C n =
      2*(((n:ℝ)+1)*(2*(n:ℝ)+9)/
        (2*((n:ℝ)+2)*((n:ℝ)+4)))*C n := by
    field_simp [ne_of_gt hpos,ne_of_gt hpos4]
    ring
  rw [hformula] at hraw
  have hscaled := mul_le_mul_of_nonneg_right hscalar hC0
  have htwice := mul_le_mul_of_nonneg_left hscaled
    (by norm_num : (0:ℝ) ≤ 2)
  dsimp [C] at *
  linarith [hraw,htwice]

end SpringerLean

#print axioms SpringerLean.halfCosMoment_succ_refined_lower
