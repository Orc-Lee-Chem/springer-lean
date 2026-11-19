import SpringerLean.Round1757LipschitzCoordinateIntegral

open MeasureTheory Filter Set

namespace SpringerLean

noncomputable def horizontalSliceDeriv (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => f (x, p.2)) p.1

/-- The horizontal derivative of a globally Lipschitz scalar field
supported in the unit square is integrable and has zero plane
integral. This is coordinatewise FTC followed by Fubini. -/
theorem integral_horizontalSliceDeriv_zero
    (f : ℝ × ℝ → ℝ) (K : NNReal) (hf : LipschitzWith K f)
    (hzero : ∀ p : ℝ × ℝ, 1 ≤ |p.1| ∨ 1 ≤ |p.2| → f p = 0) :
    Integrable (horizontalSliceDeriv f) ∧
      (∫ p : ℝ × ℝ, horizontalSliceDeriv f p) = 0 := by
  have hslice (y : ℝ) : LipschitzWith K (fun x => f (x, y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x w
    simpa [Prod.dist_eq] using hf.dist_le_mul (x, y) (w, y)
  have hbound (p : ℝ × ℝ) : ‖horizontalSliceDeriv f p‖ ≤ (K : ℝ) :=
    norm_deriv_le_of_lipschitz (hslice p.2)
  have hfamily : Continuous (fun p : ℝ × ℝ => f (p.2, p.1)) :=
    hf.continuous.comp continuous_swap
  have hmeas : Measurable (horizontalSliceDeriv f) := by
    have hm : Measurable (fun p : ℝ × ℝ =>
        deriv (fun x => f (x, p.1)) p.2) :=
      measurable_deriv_with_param (f := fun y x => f (x, y)) hfamily
    convert hm.comp measurable_swap using 1
    ext p
    rfl
  let D : Set (ℝ × ℝ) := Ioc (-2 : ℝ) 2 ×ˢ Ioc (-2 : ℝ) 2
  have hDfinite : (volume : Measure (ℝ × ℝ)) D ≠ ⊤ := by
    change ((volume : Measure ℝ).prod volume) (Ioc (-2 : ℝ) 2 ×ˢ Ioc (-2 : ℝ) 2) ≠ ⊤
    rw [Measure.prod_prod]
    simp only [Real.volume_Ioc]
    finiteness
  have hIntD : IntegrableOn (horizontalSliceDeriv f) D :=
    Measure.integrableOn_of_bounded hDfinite hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hout (p : ℝ × ℝ) (hp : p ∉ D) : horizontalSliceDeriv f p = 0 := by
    have hor : 1 < |p.1| ∨ 1 < |p.2| := by
      by_contra h
      push_neg at h
      have hx := abs_le.mp h.1
      have hy := abs_le.mp h.2
      exact hp ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩,
        ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩
    rcases hor with hx | hy
    · exact deriv_zero_outside_unit_support (fun x => f (x, p.2))
        (fun x hx => hzero (x, p.2) (Or.inl hx)) hx
    · have heq : (fun x => f (x, p.2)) = (fun _ : ℝ => (0 : ℝ)) :=
        funext (fun x => hzero (x, p.2) (Or.inr hy.le))
      simp [horizontalSliceDeriv, heq]
  have hInt : Integrable (horizontalSliceDeriv f) :=
    hIntD.integrable_of_forall_notMem_eq_zero hout
  refine ⟨hInt, ?_⟩
  have hsliceZero (y : ℝ) :
      (∫ x : ℝ, horizontalSliceDeriv f (x, y)) = 0 :=
    (integral_deriv_zero_of_lipschitz_unit_support (fun x => f (x, y)) K
      (hslice y) (fun x hx => hzero (x, y) (Or.inl hx))).2
  calc
    _ = ∫ y : ℝ, ∫ x : ℝ, horizontalSliceDeriv f (x, y) :=
      integral_prod_symm _ hInt
    _ = ∫ _ : ℝ, (0 : ℝ) :=
      integral_congr_ae (Filter.Eventually.of_forall hsliceZero)
    _ = 0 := by simp

end SpringerLean

#print axioms SpringerLean.integral_horizontalSliceDeriv_zero
