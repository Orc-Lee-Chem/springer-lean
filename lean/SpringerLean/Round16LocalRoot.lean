import SpringerLean.Round15Derivative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

open Filter
open scoped Topology

namespace SpringerLean

/-- The power map admits a strictly differentiable inverse germ at one.
The local right-inverse equation is the only root property needed below. -/
theorem exists_strict_local_pow_root (m : ℕ) (hm : 0 < m) :
    ∃ R : ℂ → ℂ,
      R 1 = 1 ∧
      HasStrictDerivAt R (m : ℂ)⁻¹ 1 ∧
      (∀ᶠ y in 𝓝 (1 : ℂ), (R y) ^ m = y) := by
  let P : ℂ → ℂ := fun z => z ^ m
  have hP : HasStrictDerivAt P (m : ℂ) 1 := by
    simpa [P] using (hasStrictDerivAt_pow m (1 : ℂ))
  have hd : (m : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hm
  let R := hP.localInverse _ _ _ hd
  have hR1 : R 1 = 1 := by
    simpa only [P, one_pow] using (hP.eventually_left_inverse hd).self_of_nhds
  have hRder : HasStrictDerivAt R (m : ℂ)⁻¹ 1 := by
    simpa only [P, one_pow] using hP.to_localInverse hd
  have hright : ∀ᶠ y in 𝓝 (1 : ℂ), (R y) ^ m = y := by
    simpa only [P, one_pow] using hP.eventually_right_inverse hd
  exact ⟨R, hR1, hRder, hright⟩

end SpringerLean
