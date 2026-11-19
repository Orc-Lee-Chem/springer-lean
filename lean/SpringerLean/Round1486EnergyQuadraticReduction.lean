import SpringerLean.Round1485PhaseCutoffBudget

namespace SpringerLean

/-- The common quadratic form appearing in every multiplier endpoint
of the signed harmonic-filling energy estimate. -/
def signedEnergyQuadratic (A B D s : ℝ) : ℝ :=
  D+B*s+(1-A)*s^2

/-- One exact completed-square test replaces repeated maximization of
the multiplier quadratic. It is valid on the whole real line, hence
also for the nonnegative slope ratio used in the energy proof. -/
theorem signedEnergyQuadratic_le_of_discriminant
    {A B D C : ℝ} (hA : 1 < A) (hD : D ≤ C)
    (hdisc : B^2 ≤ 4*(A-1)*(C-D)) (s : ℝ) :
    signedEnergyQuadratic A B D s ≤ C := by
  have hsquare : 0 ≤ (2*(A-1)*s-B)^2 := sq_nonneg _
  have hpositive : 0 < A-1 := by linarith
  have hmaster : 0 ≤ 4*(A-1)*(C-signedEnergyQuadratic A B D s) := by
    dsimp [signedEnergyQuadratic]
    nlinarith [hsquare,hdisc]
  nlinarith

/-- The degenerate multiplier segment, where the quadratic coefficient
vanishes, is checked separately. -/
theorem signedEnergyQuadratic_le_of_linear
    {B D C : ℝ} (hB : B = 0) (hD : D ≤ C) (s : ℝ) :
    signedEnergyQuadratic 1 B D s ≤ C := by
  simp [signedEnergyQuadratic,hB]
  exact hD

/-- For fixed slope ratio, the multiplier quadratic is affine in the
three coefficient entries. Therefore endpoint checks cover every
interior point of an affine segment without additional arithmetic. -/
theorem signedEnergyQuadratic_affine_endpoint
    {A₀ A₁ B₀ B₁ D₀ D₁ C q s : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h₀ : signedEnergyQuadratic A₀ B₀ D₀ s ≤ C)
    (h₁ : signedEnergyQuadratic A₁ B₁ D₁ s ≤ C) :
    signedEnergyQuadratic
      ((1-q)*A₀+q*A₁)
      ((1-q)*B₀+q*B₁)
      ((1-q)*D₀+q*D₁) s ≤ C := by
  have hcomb : signedEnergyQuadratic
      ((1-q)*A₀+q*A₁)
      ((1-q)*B₀+q*B₁)
      ((1-q)*D₀+q*D₁) s =
      (1-q)*signedEnergyQuadratic A₀ B₀ D₀ s+
      q*signedEnergyQuadratic A₁ B₁ D₁ s := by
    dsimp [signedEnergyQuadratic]
    ring
  rw [hcomb]
  have hL := mul_le_mul_of_nonneg_left h₀ (by linarith : 0 ≤ 1-q)
  have hR := mul_le_mul_of_nonneg_left h₁ hq0
  nlinarith

end SpringerLean

#print axioms SpringerLean.signedEnergyQuadratic_le_of_discriminant
#print axioms SpringerLean.signedEnergyQuadratic_affine_endpoint
