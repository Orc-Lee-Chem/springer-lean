import SpringerLean.Round1518PositivePartPowerConvex

namespace SpringerLean
set_option maxHeartbeats 320000

private def powerResidual (M : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  x^m-(M^m+(m:ℝ)*M^(m-1)*(x-M))

/-- Up to the cap height, the power minus its cap tangent decreases.
This is the monotonicity needed for the convex piecewise gluing. -/
theorem powerResidual_antitone_Icc {M : ℝ} (hM : 0 ≤ M)
    (m : ℕ) : AntitoneOn (powerResidual M m) (Set.Icc 0 M) := by
  have hcont : ContinuousOn (powerResidual M m) (Set.Icc 0 M) := by
    change ContinuousOn (fun x : ℝ => x^m-(M^m+(m:ℝ)*M^(m-1)*(x-M))) _
    fun_prop
  have hdiff : DifferentiableOn ℝ (powerResidual M m)
      (interior (Set.Icc 0 M)) := by
    change DifferentiableOn ℝ (fun x : ℝ => x^m-(M^m+(m:ℝ)*M^(m-1)*(x-M))) _
    fun_prop
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 M) hcont hdiff
  intro x hx
  have hxi : x ∈ Set.Icc 0 M := interior_subset hx
  have hx0 : 0 ≤ x := hxi.1
  have hxM : x ≤ M := hxi.2
  have hder : deriv (powerResidual M m) x =
      (m:ℝ)*x^(m-1)-(m:ℝ)*M^(m-1) := by
    apply HasDerivAt.deriv
    have hh := ((hasDerivAt_pow m x).sub_const (M^m)).sub
      (((hasDerivAt_id x).sub_const M).const_mul ((m:ℝ)*M^(m-1)))
    convert hh using 1
    · funext y
      simp [powerResidual]
      ring
    · ring
  rw [hder]
  have hp : x^(m-1) ≤ M^(m-1) := pow_le_pow_left₀ hx0 hxM _
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hp hm0]

def positivePowerResidual (M : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  (max x 0)^m-(M^m+(m:ℝ)*M^(m-1)*(x-M))

/-- The positive-part power's tangent residual decreases all the way
from negative infinity to the positive cap. -/
theorem positivePowerResidual_antitone_Iic {M : ℝ} (hM : 0 ≤ M)
    {m : ℕ} (hm : 1 ≤ m) :
    AntitoneOn (positivePowerResidual M m) (Set.Iic M) := by
  have hmne : m ≠ 0 := by omega
  have hc : 0 ≤ (m:ℝ)*M^(m-1) :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hM _)
  have hneg {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) (hxy : x ≤ y) :
      positivePowerResidual M m y ≤ positivePowerResidual M m x := by
    simp only [positivePowerResidual,max_eq_right hx,max_eq_right hy,zero_pow hmne]
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hxy)]
  have hpos {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ M) (hxy : x ≤ y) :
      positivePowerResidual M m y ≤ positivePowerResidual M m x := by
    have hp := powerResidual_antitone_Icc hM m
      (show x ∈ Set.Icc 0 M from ⟨hx,hxy.trans hy⟩)
      (show y ∈ Set.Icc 0 M from ⟨hx.trans hxy,hy⟩) hxy
    simpa [positivePowerResidual,powerResidual,
      max_eq_left hx,max_eq_left (hx.trans hxy)] using hp
  intro x hx y hy hxy
  by_cases hy0 : y ≤ 0
  · exact hneg (hxy.trans hy0) hy0 hxy
  · have hypos : 0 ≤ y := le_of_lt (lt_of_not_ge hy0)
    by_cases hx0 : 0 ≤ x
    · exact hpos hx0 hy hxy
    · have hxneg : x ≤ 0 := le_of_lt (lt_of_not_ge hx0)
      exact (hpos le_rfl hy hypos).trans (hneg hxneg le_rfl hxneg)

end SpringerLean

#print axioms SpringerLean.powerResidual_antitone_Icc
#print axioms SpringerLean.positivePowerResidual_antitone_Iic
