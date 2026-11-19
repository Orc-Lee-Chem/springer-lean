import SpringerLean.Round1816ReferenceDiskIntegral
import SpringerLean.Round1818ReferenceTailPointwise

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 800000

def normalizedReferenceTest (m : ℕ) (c x : ℝ) : ℝ :=
  max ((max x 0)^m) (c^8*(max x 0)^(m-8))

theorem twoPowerPhaseTest_normalized (j : ℕ) (c x : ℝ) :
    twoPowerPhaseTest (2*c) j (2*x)/(2 : ℝ)^(j+10)=
      normalizedReferenceTest (j+10) c x := by
  have hmax : max (2*x) 0=2*max x 0 := by
    rw [mul_max_of_nonneg x 0 (by norm_num : (0 : ℝ) ≤ 2),mul_zero]
  have hp : (2 : ℝ)^(j+10)=(2 : ℝ)^8*(2 : ℝ)^(j+2) := by
    rw [←pow_add]
    congr 1
    omega
  unfold twoPowerPhaseTest normalizedReferenceTest
  rw [hmax,←max_div_div_right (by positivity : (0 : ℝ) ≤ 2^(j+10))]
  have h₁ : (2*max x 0)^(j+10)/(2 : ℝ)^(j+10)=(max x 0)^(j+10) := by
    rw [mul_pow]
    field_simp
  have h₂ : (2*c)^8*(2*max x 0)^(j+2)/(2 : ℝ)^(j+10)=c^8*(max x 0)^(j+2) := by
    rw [mul_pow,mul_pow,hp]
    field_simp
    <;> ring
  rw [h₁,h₂]
  rw [show j+10-8=j+2 by omega]

theorem normalizedReferenceTest_excess (m : ℕ) (hm : 9 ≤ m)
    {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    normalizedReferenceTest m c x-(max x 0)^m=
      if 0 < x ∧ x < c then x^(m-8)*(c^8-x^8) else 0 := by
  have hm0 : m ≠ 0 := by omega
  have hell0 : m-8 ≠ 0 := by omega
  by_cases hx : 0 < x
  · have hmax : max x 0=x := max_eq_left hx.le
    have hpow : x^m=x^(m-8)*x^8 := by rw [←pow_add]; congr 1; omega
    unfold normalizedReferenceTest
    rw [hmax]
    by_cases hxc : x < c
    · rw [if_pos ⟨hx,hxc⟩]
      have hh : x^m ≤ c^8*x^(m-8) := by
        rw [hpow]
        have hp := pow_le_pow_left₀ hx.le hxc.le 8
        nlinarith [mul_le_mul_of_nonneg_left hp (pow_nonneg hx.le (m-8))]
      rw [max_eq_right hh,hpow]
      ring
    · rw [if_neg (by tauto)]
      have hh : c^8*x^(m-8) ≤ x^m := by
        rw [hpow]
        have hp := pow_le_pow_left₀ hc (le_of_not_gt hxc) 8
        nlinarith [mul_le_mul_of_nonneg_left hp (pow_nonneg hx.le (m-8))]
      rw [max_eq_left hh,sub_self]
  · have hmax : max x 0=0 := max_eq_right (le_of_not_gt hx)
    simp only [normalizedReferenceTest,hmax,zero_pow hm0,zero_pow hell0,mul_zero,
      max_self,sub_self,if_neg (by tauto : ¬(0 < x ∧ x < c))]

end
end SpringerLean

#print axioms SpringerLean.twoPowerPhaseTest_normalized
#print axioms SpringerLean.normalizedReferenceTest_excess
