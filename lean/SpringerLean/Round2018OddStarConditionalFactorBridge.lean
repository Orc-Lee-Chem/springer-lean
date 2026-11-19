import SpringerLean.Round2017OddStarRegularBaseline

open MeasureTheory

namespace SpringerLean

/-- The exact capacity-one PR2 formula after identifying the actual
radial boundary law with the equilibrium measure. This is an explicit
remaining hypothesis, not a proved assertion in this module. -/
def OddStarRadialFactorFormula (m : ℕ) : Prop :=
  ∀ t : ℝ, |t| < 1 →
    factorConstant (oddStarPerturbationOmitted m t) =
      Real.exp (∫ z : ℂ,
        Real.log (continuumFarthestDistance
          (oddStarPerturbationOmitted m t) z)
        ∂oddStarActualBoundaryProbability m t)

/-- Exact conditional reduction of the odd factor-constant conclusion.
The additional PR2/equilibrium premise remains open in the Lean source. -/
theorem oddStarFactorConstant_strict_of_radialFormula
    (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m)
    (hformula : OddStarRadialFactorFormula m) :
    ∃ t : ℝ, 0 < t ∧ |t| < 1 ∧
      factorConstant (oddStarPerturbationOmitted m 0) <
        factorConstant (oddStarPerturbationOmitted m t) := by
  obtain ⟨t, htpos, ht1, hlt⟩ :=
    oddStarActualBoundaryProbability_exists_strict_farthestLog_over_regular
      m hm hodd
  refine ⟨t, htpos, ht1, ?_⟩
  rw [hformula 0 (by norm_num), hformula t ht1]
  exact Real.exp_strictMono hlt

end SpringerLean

#check @SpringerLean.oddStarFactorConstant_strict_of_radialFormula
#print axioms SpringerLean.oddStarFactorConstant_strict_of_radialFormula
