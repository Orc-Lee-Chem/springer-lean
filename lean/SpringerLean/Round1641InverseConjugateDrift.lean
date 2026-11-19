import SpringerLean.Round1640ActualExplicitSFlux

open scoped ComplexConjugate

namespace SpringerLean

/-- The inverse-conjugate drift field is the real vector H/|H|²,
including both Cartesian components used by the phase flux. -/
theorem inverseConjugate_dot_gradient
    (H : ℂ) (ux uy : ℝ) :
    ((conj H)⁻¹).re*ux+((conj H)⁻¹).im*uy =
      (H.re*ux+H.im*uy)/‖H‖^2 := by
  rw [inverseConjugate_eq_div_normSq, Complex.normSq_eq_norm_sq]
  simp only [Complex.div_ofReal_re, Complex.div_ofReal_im]
  ring

end SpringerLean

#print axioms SpringerLean.inverseConjugate_dot_gradient
