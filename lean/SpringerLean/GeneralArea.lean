import SpringerLean.AreaFinite

namespace SpringerLean

/-- The complete general `k=1` upper bound for the actual inverse
coefficient of every map in the paper's centered exterior class. -/
theorem exteriorInverseCoeff_one_norm_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorInverseCoeff F 1‖ ≤ 1 := by
  rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc]
  exact exteriorForwardCoeff_one_norm_le_of_finite_area F
    (fun N => exteriorForwardCoeff_finite_area F hc N)

/-- The complete `k=1` equality classification on the actual exterior
domain. The paper's function class imposes no values inside the unit disk,
so equality is correctly expressed as `EqOn exteriorDisk`. -/
theorem exteriorInverseCoeff_one_norm_eq_one_iff_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorInverseCoeff F 1‖ = 1 ↔
      ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk :=
  exteriorInverseCoeff_one_norm_eq_one_iff_slit_of_finite_area
    F hc (fun N => exteriorForwardCoeff_finite_area F hc N)

end SpringerLean
