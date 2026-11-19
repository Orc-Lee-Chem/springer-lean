import SpringerLean.Round1997OddStarTipGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace SpringerLean

/-- The tip radius of the explicit odd-star perturbation. -/
noncomputable def oddStarTipRadius (m : ℕ) (t : ℝ) : ℝ :=
  (4 * Real.sqrt (1 - t ^ 2)) ^ ((m : ℝ)⁻¹)

/-- The moving tip has zero first-order displacement at the regular
star t = 0. -/
theorem oddStarTipRadius_hasDerivAt_zero
    (m : ℕ) (hm : 3 ≤ m) :
    HasDerivAt (oddStarTipRadius m) 0 0 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hbase : HasDerivAt (fun t : ℝ => 1 - t ^ 2) 0 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
      ((hasDerivAt_id (0 : ℝ)).pow 2) using 1 <;>
        norm_num <;> (funext t; rfl)
  have hsqrt : HasDerivAt Real.sqrt (1 / 2) (1 : ℝ) := by
    simpa using Real.hasDerivAt_sqrt (by norm_num : (1 : ℝ) ≠ 0)
  have hroot : HasDerivAt (fun t : ℝ => Real.sqrt (1 - t ^ 2)) 0 0 := by
    have hsqrt0 : HasDerivAt Real.sqrt (1 / 2) (1 - (0 : ℝ) ^ 2) := by
      simpa using hsqrt
    convert hsqrt0.comp 0 hbase using 1 <;>
      norm_num <;> (funext t; rfl)
  have hinner : HasDerivAt
      (fun t : ℝ => 4 * Real.sqrt (1 - t ^ 2)) 0 0 := by
    convert (hasDerivAt_const (0 : ℝ) (4 : ℝ)).mul hroot using 1 <;>
      norm_num
  have houter : DifferentiableAt ℝ (fun x : ℝ => x ^ ((m : ℝ)⁻¹)) 4 :=
    Real.differentiableAt_rpow_const_of_ne _ (by norm_num)
  have houter0 : HasDerivAt (fun x : ℝ => x ^ ((m : ℝ)⁻¹))
      (deriv (fun x : ℝ => x ^ ((m : ℝ)⁻¹)) 4)
      (4 * Real.sqrt (1 - (0 : ℝ) ^ 2)) := by
    simpa using houter.hasDerivAt
  have hcomp := houter0.comp 0 hinner
  convert hcomp using 1
  · funext t
    rfl
  · simp

end SpringerLean

#print axioms SpringerLean.oddStarTipRadius_hasDerivAt_zero
