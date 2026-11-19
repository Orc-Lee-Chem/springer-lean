import SpringerLean.Round2141DiskEmbeddingImprovement
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.MeanValue

open Set Metric Complex

namespace SpringerLean

/-- Primitives of holomorphic functions give branches of square roots
by integrating the logarithmic derivative. -/
theorem hasHolomorphicSquareRootBranches_of_primitives
    {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U)
    (hExact : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → Complex.IsExactOn f U) :
    HasHolomorphicSquareRootBranches U := by
  intro q hq hn
  obtain ⟨x,hx⟩ := hc.nonempty
  let f := fun z => deriv q z / q z
  have hfd : DifferentiableOn ℂ f U := (hq.deriv hU).div hq hn
  obtain ⟨P,hPx,hP⟩ := (hExact f hfd).with_val_at x (Complex.log (q x))
  have hd : DifferentiableOn ℂ P U :=
    fun z hz => (hP z hz).differentiableAt.differentiableWithinAt
  let H (z : ℂ) := q z * Complex.exp (-P z)
  have hH (z : ℂ) (hz : z ∈ U) : HasDerivAt H 0 z := by
    have he := (Complex.hasDerivAt_exp (-P z)).comp z (hP z hz).neg
    have hh := (hq.hasDerivAt (hU.mem_nhds hz)).mul he
    convert hh using 1
    · ext w
      rfl
    · change 0 = deriv q z * Complex.exp (-P z) + q z * (Complex.exp (-P z) * -(deriv q z/q z))
      field_simp [hn z hz] <;> ring
  have hHd : DifferentiableOn ℂ H U :=
    fun z hz => (hH z hz).differentiableAt.differentiableWithinAt
  have hHx : H x = 1 := by
    change q x * Complex.exp (-P x) = 1
    rw [hPx,Complex.exp_neg,Complex.exp_log (hn x hx),mul_inv_cancel₀ (hn x hx)]
  have hE (z : ℂ) (hz : z ∈ U) : Complex.exp (P z) = q z := by
    have he := hU.is_const_of_deriv_eq_zero hc.isPreconnected hHd (fun y hy => (hH y hy).deriv) hx hz
    rw [hHx] at he
    change 1 = q z * Complex.exp (-P z) at he
    rw [Complex.exp_neg,←div_eq_mul_inv] at he
    exact ((div_eq_iff (Complex.exp_ne_zero _)).mp he.symm |>.trans (one_mul _)).symm
  let g (z : ℂ) := Complex.exp (P z / 2)
  have hg : DifferentiableOn ℂ g U := Complex.differentiable_exp.comp_differentiableOn (hd.div_const _)
  refine ⟨g,hg,fun z hz => ?_⟩
  change Complex.exp (P z/2)^2 = q z
  rw [pow_two,←Complex.exp_add,show P z/2+P z/2 = P z by ring,hE z hz]

end SpringerLean
