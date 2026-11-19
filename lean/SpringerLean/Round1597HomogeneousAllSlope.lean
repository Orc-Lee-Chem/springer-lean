import SpringerLean.Round1596ActualPhaseDriftPDE

namespace SpringerLean

/-- A quadratic bounded above on every nonnegative slope cannot have
a positive leading coefficient. This derives A ≥ 1 from the same
all-slope certificate, so the p=0 case needs no extra hypothesis. -/
theorem signedEnergyQuadratic_A_ge_one
    {A B D C : ℝ}
    (hquad : ∀ s : ℝ, 0 ≤ s → signedEnergyQuadratic A B D s ≤ C) :
    1 ≤ A := by
  by_contra hA
  have hc : 0 < 1-A := by linarith
  let s : ℝ := 1+(|B|+|D-C|+1)/(1-A)
  have hs : 1 ≤ s := by
    dsimp [s]
    have hnum : 0 ≤ |B|+|D-C|+1 := by positivity
    have hdiv := div_nonneg hnum (le_of_lt hc)
    linarith
  have hcs : (1-A)*s = (1-A)+|B|+|D-C|+1 := by
    dsimp [s]
    field_simp [ne_of_gt hc]
    ring
  have hq := hquad s (by linarith : 0 ≤ s)
  dsimp [signedEnergyQuadratic] at hq
  have hB : -|B| ≤ B := neg_abs_le B
  have hDC : -|D-C| ≤ D-C := neg_abs_le (D-C)
  have hp₁ : 0 ≤ (s-1)*|D-C| :=
    mul_nonneg (by linarith) (abs_nonneg _)
  have hp₂ : 0 ≤ s*(B+|B|) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hcs, hq, hp₁, hp₂]

/-- The homogeneous inequality, including p=0, now follows solely
from the all-slope scalar certificate. -/
theorem signedEnergyQuadratic_homogeneous_of_all_s
    {A B D C p v : ℝ} (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hquad : ∀ s : ℝ, 0 ≤ s → signedEnergyQuadratic A B D s ≤ C) :
    D*p^2+B*v*p+(1-A)*v^2 ≤ C*p^2 := by
  exact signedEnergyQuadratic_homogeneous
    (signedEnergyQuadratic_A_ge_one hquad) hp hv hquad

end SpringerLean

#print axioms SpringerLean.signedEnergyQuadratic_A_ge_one
#print axioms SpringerLean.signedEnergyQuadratic_homogeneous_of_all_s
