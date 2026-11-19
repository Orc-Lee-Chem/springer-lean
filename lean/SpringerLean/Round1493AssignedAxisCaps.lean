import SpringerLean.Round1492SelectedFineWidths

open scoped ComplexConjugate

namespace SpringerLean

/-- The radius-maximality data carried by the selected endpoints give
exact projection caps on the entire first hull and on the assigned
negative half for the second endpoint. -/
theorem selectedEndpoints_assigned_axis_caps
    (F : ℂ → ℂ) (P₁ P₂ : ℂ)
    (hP₁0 : 0 < ‖P₁‖) (hP₂0 : 0 < ‖P₂‖)
    (hmax₁ : ∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖)
    (hmax₂ : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) :
    (∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ ‖P₁‖) ∧
    (∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 0 →
      (conj (P₂/(‖P₂‖:ℂ))*w).re ≤ ‖P₂‖) := by
  have hunit₁ : ‖P₁/(‖P₁‖:ℂ)‖=1 := by
    simp [norm_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hP₁0,ne_of_gt hP₁0]
  have hunit₂ : ‖P₂/(‖P₂‖:ℂ)‖=1 := by
    simp [norm_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hP₂0,ne_of_gt hP₂0]
  constructor
  · intro w hw
    calc
      (conj (P₁/(‖P₁‖:ℂ))*w).re ≤
          ‖conj (P₁/(‖P₁‖:ℂ))*w‖ := Complex.re_le_norm _
      _ = ‖w‖ := by rw [norm_mul,Complex.norm_conj,hunit₁,one_mul]
      _ ≤ ‖P₁‖ := hmax₁ w hw
  · intro w hw hneg
    calc
      (conj (P₂/(‖P₂‖:ℂ))*w).re ≤
          ‖conj (P₂/(‖P₂‖:ℂ))*w‖ := Complex.re_le_norm _
      _ = ‖w‖ := by rw [norm_mul,Complex.norm_conj,hunit₂,one_mul]
      _ ≤ ‖P₂‖ := hmax₂ w hw hneg

end SpringerLean

#print axioms SpringerLean.selectedEndpoints_assigned_axis_caps
