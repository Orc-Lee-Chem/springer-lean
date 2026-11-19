import SpringerLean.Round1365ConvexChordExtension

namespace SpringerLean

/-- The exact profile used for a bad selected endpoint: keep the
original power to `x₀`, then continue by its chord to `μ`. -/
noncomputable def coarseInverseChordPower
    (n : ℕ) (x₀ μ x : ℝ) : ℝ :=
  if x ≤ x₀ then coarseInverseRadius x ^ n else
    coarseInverseRadius x₀ ^ n +
      (x-x₀)/(μ-x₀)*
        (coarseInverseRadius μ ^ n-coarseInverseRadius x₀ ^ n)

theorem coarseInverseChordPower_convexOn
    (n : ℕ) {x₀ μ : ℝ} (h₀μ : x₀ < μ) :
    ConvexOn ℝ Set.univ
      (coarseInverseChordPower n x₀ μ) := by
  change ConvexOn ℝ Set.univ (fun x =>
    if x ≤ x₀ then coarseInverseRadius x ^ n else
      coarseInverseRadius x₀ ^ n +
        (x-x₀)/(μ-x₀)*
          (coarseInverseRadius μ ^ n-coarseInverseRadius x₀ ^ n))
  exact convexProfile_right_chord_extension
    (fun x => coarseInverseRadius x ^ n)
    (coarseInverseRadius_pow_convexOn n) h₀μ

/-- On every actual projection below the mean `μ`, the chord profile
majorizes the original exact profile. -/
theorem coarseInversePower_le_chordPower
    (n : ℕ) {x₀ μ x : ℝ} (h₀μ : x₀ < μ) (hxμ : x ≤ μ) :
    coarseInverseRadius x ^ n ≤ coarseInverseChordPower n x₀ μ x := by
  by_cases hx₀ : x ≤ x₀
  · simp [coarseInverseChordPower, hx₀]
  · have hx₀' : x₀ ≤ x := le_of_lt (lt_of_not_ge hx₀)
    simp only [coarseInverseChordPower, if_neg hx₀]
    exact coarseInversePower_le_chord n h₀μ hx₀' hxμ

end SpringerLean

#print axioms SpringerLean.coarseInverseChordPower_convexOn
#print axioms SpringerLean.coarseInversePower_le_chordPower
