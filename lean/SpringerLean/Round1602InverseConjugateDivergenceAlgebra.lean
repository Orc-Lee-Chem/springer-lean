import SpringerLean.Round1601PhaseFluxSProductRule

open scoped ComplexConjugate

namespace SpringerLean

/-- Algebraic divergence of the inverse-conjugate field.  For
`H=z+g(conj z)`, `Q=(conj H)⁻¹=H/|H|²`; the two displayed complex
numbers are its Cartesian derivatives. -/
theorem inverseConjugate_divergence_algebra
    (H c : ℂ) (hH : H ≠ 0) :
    (-(conj (1+c))/(conj H)^2).re +
      (-(conj (Complex.I*(1-c)))/(conj H)^2).im =
      -2*(c/H^2).re := by
  have hHc : conj H ≠ 0 := by
    intro hz
    apply hH
    have hz' := congrArg conj hz
    simpa using hz'
  have hcombine :
      -(conj (1+c))/(conj H)^2 -
        Complex.I*(-(conj (Complex.I*(1-c)))/(conj H)^2) =
      -2*conj (c/H^2) := by
    simp only [map_add, map_sub, map_one, map_mul,
      Complex.conj_I, map_div₀, map_pow]
    field_simp [hHc]
    simp only [Complex.I_sq]
    ring
  have hre := congrArg Complex.re hcombine
  have hreal : ((conj c)/(conj H)^2).re = (c/H^2).re := by
    have heq : (conj c)/(conj H)^2 = conj (c/H^2) := by simp
    exact (congrArg Complex.re heq).trans (Complex.conj_re _)
  simpa [Complex.sub_re, Complex.mul_re, hreal] using hre

end SpringerLean

#print axioms SpringerLean.inverseConjugate_divergence_algebra
