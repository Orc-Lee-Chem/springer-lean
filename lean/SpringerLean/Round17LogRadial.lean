import SpringerLean.Round17CauchyKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace SpringerLean

/-- The radial real logarithm used to isolate the horizontal displacement
of a vertical-line logarithmic potential. -/
noncomputable def verticalLogRadial (b t : ℝ) : ℝ :=
  Real.log (t ^ 2 + b ^ 2) / 2

/-- For a nonzero vertical coordinate, the difference of two radial
logarithms is an interval integral of the positive Cauchy kernel. This
also covers `b=0`; the excluded single point is irrelevant to Lebesgue
integration over the vertical line. -/
theorem verticalLogRadial_sub_one_eq_intervalIntegral
    (b t : ℝ) (ht : t ≠ 0) :
    verticalLogRadial b t - verticalLogRadial 1 t =
      ∫ lam : ℝ in (1 : ℝ)..b, lam / (lam ^ 2 + t ^ 2) := by
  calc
    _ = (Real.log (t ^ 2 + b ^ 2) - Real.log (t ^ 2 + (1 : ℝ) ^ 2)) / 2 := by
      simp only [verticalLogRadial]
      ring
    _ = ∫ lam : ℝ in (1 : ℝ)..b, lam / (t ^ 2 + lam ^ 2) :=
      (integral_id_div_sq_add_sq (a := (1 : ℝ)) (b := b) (c := t) ht).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro lam _
      change lam / (t ^ 2 + lam ^ 2) = lam / (lam ^ 2 + t ^ 2)
      rw [add_comm]

end SpringerLean
