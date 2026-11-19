import SpringerLean.Round1431RefinedVariableChord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace SpringerLean
set_option maxHeartbeats 200000

/-- The moving chord passes through a mean projection at least as far
right as the actual endpoint radius `2-d`. -/
theorem refinedArc_mean_bounds
    {d : ℝ} (hd0 : 0 < d) (hd : d ≤ 1/1501) :
    let b : ℝ := Real.sqrt (3*d)
    let x₀ : ℝ := 2*Real.cos b
    let μ : ℝ := 2*Real.sin b/b
    0 < b ∧ b ≤ Real.pi/2 ∧ x₀ < μ ∧
      2-d ≤ μ ∧ μ ≤ 2 := by
  dsimp
  let b : ℝ := Real.sqrt (3*d)
  have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
  have hbSq : b^2=3*d := Real.sq_sqrt (by positivity)
  have hbSmall : b ≤ 1 := by
    have hsmall : 3*d≤1 := by nlinarith
    nlinarith [hbSq]
  have hbhalf : b ≤ Real.pi/2 := by
    linarith [Real.pi_gt_three]
  have hbpi : |b| ≤ Real.pi := by
    rw [abs_of_pos hb]
    linarith [Real.pi_gt_three]
  have hsin := Real.sin_gt_sub_cube hb
  have hcos := Real.cos_le_one_sub_mul_cos_sq hbpi
  have hpiSq : Real.pi^2 < 10 := by
    have hpipos : 0 < Real.pi := Real.pi_pos
    have hpi3 := Real.pi_lt_d2
    nlinarith [sq_nonneg (Real.pi-(315/100:ℝ))]
  have hpic : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have hcosWeak : Real.cos b ≤ 1-b^2/5 := by
    have hcoef : (1/5:ℝ) ≤ 2/Real.pi^2 := by
      apply (le_div_iff₀ hpic).2
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg b)]
  have hsinDiv : 1-b^2/6 < Real.sin b/b := by
    apply (lt_div_iff₀ hb).2
    nlinarith [hsin]
  have hmeanLower : 2-d < 2*Real.sin b/b := by
    have hdiv : b^2/3=d := by rw [hbSq]; ring
    have htwo : 2*(Real.sin b/b)=2*Real.sin b/b := by ring
    rw [← htwo]
    nlinarith
  have hxμ : 2*Real.cos b < 2*Real.sin b/b := by
    have htwo : 2*(Real.sin b/b)=2*Real.sin b/b := by ring
    rw [← htwo]
    nlinarith [sq_pos_of_pos hb]
  have hmeanUpper : 2*Real.sin b/b ≤ 2 := by
    have hsinLe := Real.sin_le hb.le
    apply (div_le_iff₀ hb).2
    nlinarith
  exact ⟨hb,hbhalf,hxμ,hmeanLower.le,hmeanUpper⟩

/-- The variable arc mean identity at `b=sqrt(3d)`. The angular mean
`2 sin b/b` also dominates the actual endpoint radius. -/
theorem refinedAffineChord_moving_arc_mean_identity
    (W : ℝ) (n : ℕ) {d : ℝ}
    (hd0 : 0 < d) (hd : d ≤ 1/1501) :
    let b : ℝ := Real.sqrt (3*d)
    let x₀ : ℝ := 2*Real.cos b
    let μ : ℝ := 2*Real.sin b/b
    let V : ℝ := Real.circleAverage
      (fun ζ : ℂ => refinedAffineRadius W (2*ζ.re)^n) 0 1
    let T : ℝ := Real.circleAverage
      (fun ζ : ℂ => refinedAffineChordPower W n x₀ μ (2*ζ.re)) 0 1
    V-T = (b/Real.pi)*
      ((1/b)*(∫ θ in (0:ℝ)..b,
        refinedAffineRadius W (2*Real.cos θ)^n) -
        refinedAffineRadius W μ^n) := by
  have hmean := refinedArc_mean_bounds hd0 hd
  have h := refinedAffineChord_exact_arc_identity W n
    hmean.1 hmean.2.1 hmean.2.2.1
  dsimp at h ⊢
  rw [h]
  have hb : Real.sqrt (3*d) ≠ 0 := ne_of_gt hmean.1
  field_simp [hb]

end SpringerLean

#print axioms SpringerLean.refinedArc_mean_bounds
#print axioms SpringerLean.refinedAffineChord_moving_arc_mean_identity
