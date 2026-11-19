import SpringerLean.OuterSimplified

open MeasureTheory

namespace SpringerLean

/-- The exact radial contribution of the `j`th negative derivative mode. -/
theorem exteriorRadialMode_integral
    {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) (j : ℕ) :
    (∫ ρ in r..R,
      2 * (j : ℝ) ^ 2 * (ρ⁻¹) ^ (2 * j + 1)) =
      (j : ℝ) * ((r⁻¹) ^ (2 * j) - (R⁻¹) ^ (2 * j)) := by
  let G : ℝ → ℝ := fun ρ => -((j : ℝ) * (ρ⁻¹) ^ (2 * j))
  have hderiv : ∀ ρ ∈ Set.uIcc r R,
      HasDerivAt G (2 * (j : ℝ) ^ 2 * (ρ⁻¹) ^ (2 * j + 1)) ρ := by
    intro ρ hρ
    have hρpos : 0 < ρ := by
      rw [Set.uIcc_of_le hR] at hρ
      exact lt_of_lt_of_le hr hρ.1
    have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-(ρ ^ 2)⁻¹) ρ :=
      hasDerivAt_inv hρpos.ne'
    have hpow : HasDerivAt (fun x : ℝ => (x⁻¹) ^ (2 * j))
        ((2 * j : ℝ) * (ρ⁻¹) ^ (2 * j - 1) * (-(ρ ^ 2)⁻¹)) ρ := by
      convert (hasDerivAt_pow (2 * j) (ρ⁻¹)).comp ρ hinv using 1
      · ext x; rfl
      · push_cast; ring
    have hG := hpow.const_mul (-(j : ℝ))
    convert hG using 1
    · ext x
      simp [G]
    · have hρ0 : ρ ≠ 0 := hρpos.ne'
      by_cases hj : j = 0
      · subst j
        simp
      · have hj1 : 1 ≤ 2 * j := by omega
        have he : (ρ⁻¹) ^ (2 * j - 1) * (ρ ^ 2)⁻¹ =
            (ρ⁻¹) ^ (2 * j + 1) := by
          rw [← inv_pow, ← pow_add]
          congr 1
          omega
        rw [show -(j : ℝ) * ((2 * j : ℝ) * (ρ⁻¹) ^ (2 * j - 1) * (-(ρ ^ 2)⁻¹)) =
          (j : ℝ) * (2 * j : ℝ) *
            ((ρ⁻¹) ^ (2 * j - 1) * (ρ ^ 2)⁻¹) by ring, he]
        ring
  have hcont : ContinuousOn
      (fun ρ : ℝ => 2 * (j : ℝ) ^ 2 * (ρ⁻¹) ^ (2 * j + 1))
      (Set.uIcc r R) := by
    have hinvcont : ContinuousOn (fun ρ : ℝ => ρ⁻¹) (Set.uIcc r R) := by
      intro ρ hρ
      have hρpos : 0 < ρ := by
        rw [Set.uIcc_of_le hR] at hρ
        exact lt_of_lt_of_le hr hρ.1
      exact (continuousAt_inv₀ hρpos.ne').continuousWithinAt
    exact (hinvcont.pow (2 * j + 1)).const_mul _
  have hint := hcont.intervalIntegrable (μ := MeasureTheory.volume)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  dsimp [G] at hFTC
  convert hFTC using 1
  ring

/-- The finite radial Fourier energy integrates to exactly the finite area
correction. This statement uses only finitely many actual forward coefficients. -/
theorem exteriorRadialFiniteEnergy_integral
    (F : ℂ → ℂ) {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) (N : ℕ) :
    (∫ ρ in r..R,
      2 * ρ + ∑ j ∈ Finset.Icc 1 N,
        ‖exteriorForwardCoeff F j‖ ^ 2 *
          (2 * (j : ℝ) ^ 2 * (ρ⁻¹) ^ (2 * j + 1))) =
      R ^ 2 - r ^ 2 +
        ∑ j ∈ Finset.Icc 1 N,
          (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2 *
            ((r⁻¹) ^ (2 * j) - (R⁻¹) ^ (2 * j)) := by
  have hbase : IntervalIntegrable (fun ρ : ℝ => 2 * ρ)
      MeasureTheory.volume r R := by
    exact (continuous_const.mul continuous_id).intervalIntegrable r R
  have hmode (j : ℕ) : IntervalIntegrable
      (fun ρ : ℝ => ‖exteriorForwardCoeff F j‖ ^ 2 *
        (2 * (j : ℝ) ^ 2 * (ρ⁻¹) ^ (2 * j + 1)))
      MeasureTheory.volume r R := by
    have hcont : ContinuousOn
        (fun ρ : ℝ => 2 * (j : ℝ) ^ 2 * (ρ⁻¹) ^ (2 * j + 1))
        (Set.uIcc r R) := by
      have hinvcont : ContinuousOn (fun ρ : ℝ => ρ⁻¹) (Set.uIcc r R) := by
        intro ρ hρ
        have hρpos : 0 < ρ := by
          rw [Set.uIcc_of_le hR] at hρ
          exact lt_of_lt_of_le hr hρ.1
        exact (continuousAt_inv₀ hρpos.ne').continuousWithinAt
      exact (hinvcont.pow (2 * j + 1)).const_mul _
    exact (hcont.const_mul _).intervalIntegrable
  have hsum : IntervalIntegrable
      (fun ρ : ℝ => ∑ j ∈ Finset.Icc 1 N,
        ‖exteriorForwardCoeff F j‖ ^ 2 *
          (2 * (j : ℝ) ^ 2 * (ρ⁻¹) ^ (2 * j + 1)))
      MeasureTheory.volume r R := by
    convert (IntervalIntegrable.sum (Finset.Icc 1 N)
      (fun j hj => hmode j)) using 1
    ext ρ
    simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_add hbase hsum,
    intervalIntegral.integral_finsetSum (fun j hj => hmode j)]
  have hfirst :
      (∫ ρ in r..R, 2 * ρ) = R ^ 2 - r ^ 2 := by
    have hderiv : ∀ ρ ∈ Set.uIcc r R,
        HasDerivAt (fun x : ℝ => x ^ 2) (2 * ρ) ρ := by
      intro ρ _
      convert hasDerivAt_pow 2 ρ using 1
      ring
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hbase
  rw [hfirst]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [intervalIntegral.integral_const_mul,
    exteriorRadialMode_integral hr hR j]
  ring

/-- Integrability of the same finite radial energy on the open radius
interval, needed to compare the real integral with Tonelli's lintegral. -/
theorem exteriorRadialFiniteEnergy_integrableOn
    (F : ℂ → ℂ) {r R : ℝ} (hr : 0 < r) (_hR : r ≤ R) (N : ℕ) :
    IntegrableOn
      (fun ρ : ℝ => 2 * ρ + ∑ j ∈ Finset.Icc 1 N,
        ‖exteriorForwardCoeff F j‖ ^ 2 *
          (2 * (j : ℝ) ^ 2 * (ρ⁻¹) ^ (2 * j + 1)))
      (Set.Ioo r R) := by
  have hinvcont : ContinuousOn (fun ρ : ℝ => ρ⁻¹) (Set.Icc r R) := by
    intro ρ hρ
    have hρpos : 0 < ρ := lt_of_lt_of_le hr hρ.1
    exact (continuousAt_inv₀ hρpos.ne').continuousWithinAt
  have hmode (j : ℕ) : ContinuousOn
      (fun ρ : ℝ => ‖exteriorForwardCoeff F j‖ ^ 2 *
        (2 * (j : ℝ) ^ 2 * (ρ⁻¹) ^ (2 * j + 1)))
      (Set.Icc r R) := by
    exact ((hinvcont.pow (2 * j + 1)).const_mul _).const_mul _
  have hsum : ContinuousOn
      (fun ρ : ℝ => ∑ j ∈ Finset.Icc 1 N,
        ‖exteriorForwardCoeff F j‖ ^ 2 *
          (2 * (j : ℝ) ^ 2 * (ρ⁻¹) ^ (2 * j + 1)))
      (Set.Icc r R) := by
    convert continuousOn_finsetSum (Finset.Icc 1 N)
      (fun j hj => hmode j) using 1
  have hcont : ContinuousOn
      (fun ρ : ℝ => 2 * ρ + ∑ j ∈ Finset.Icc 1 N,
        ‖exteriorForwardCoeff F j‖ ^ 2 *
          (2 * (j : ℝ) ^ 2 * (ρ⁻¹) ^ (2 * j + 1)))
      (Set.Icc r R) :=
    (continuousOn_const.mul continuousOn_id).add hsum
  exact (integrableOn_Icc_iff_integrableOn_Ioo).mp hcont.integrableOn_Icc

end SpringerLean
