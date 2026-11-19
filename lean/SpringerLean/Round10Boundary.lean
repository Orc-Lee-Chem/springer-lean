import SpringerLean.Round10Period

open MeasureTheory

namespace SpringerLean

/-- The boundary integral of the Green primitive along a parametrized curve.
The tangent is taken in the increasing angular direction. -/
noncomputable def greenBoundary (φ : ℂ → ℝ) (c : ℝ → ℂ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    greenPrimitive φ ((c θ).re, (c θ).im) *
      deriv (fun t : ℝ => (c t).im) θ

theorem greenBoundary_const (φ : ℂ → ℝ) (w : ℂ) :
    greenBoundary φ (fun _ : ℝ => w) = 0 := by
  simp [greenBoundary]

/-- The actual harmonic filling and actual exterior dilate give the same
oriented boundary integral on the unit circle. -/
theorem regular_greenBoundary_unit_eq
    (F : ℂ → ℂ) {s : ℝ} (hs : 0 < s) (φ : ℂ → ℝ) :
    greenBoundary φ (fun θ => regularHarmonic s F (greenPolar 1 θ)) =
      greenBoundary φ (fun θ => rescaleExterior s F (greenPolar 1 θ)) := by
  unfold greenBoundary
  have hc := regularHarmonic_boundary_curve_eq F hs
  have hcurves :
      (fun θ : ℝ => regularHarmonic s F (greenPolar 1 θ)) =
      (fun θ : ℝ => rescaleExterior s F (greenPolar 1 θ)) := by
    simpa [greenPolar] using hc
  rw [hcurves]

/-- The innermost polar circle of the harmonic disk has zero boundary
contribution because its parametrization is constant. -/
theorem regular_greenBoundary_disk_center
    (F : ℂ → ℂ) (s : ℝ) (φ : ℂ → ℝ) :
    greenBoundary φ (fun θ => regularHarmonic s F (greenPolar 0 θ)) = 0 := by
  have hzero : (fun θ : ℝ => regularHarmonic s F (greenPolar 0 θ)) =
      (fun _ : ℝ => regularHarmonic s F 0) := by
    funext θ
    simp [greenPolar]
  rw [hzero]
  exact greenBoundary_const φ _

/-- The existing geometric cutoff bound applies to every point of the
explicit outer-circle homotopy used by the parameter Green formula. -/
theorem regular_outer_cutoff_vanish_polar
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (T : ℝ) (hT : 0 ≤ T) (k : ℕ) :
    ∃ R : ℝ, 1 < R ∧
      (∀ θ : ℝ,
        evenWeightCutoff T hT k
          (rescaleExterior s F (greenPolar R θ)) = 0) ∧
      (∀ (θ t : ℝ), 0 ≤ t → t ≤ 1 →
        evenWeightCutoff T hT k
          (greenPolar R θ +
            (t : ℂ) * (rescaleExterior s F (greenPolar R θ) -
              greenPolar R θ)) = 0) := by
  obtain ⟨R, hR, hfar⟩ :=
    regular_evenWeightCutoff_far_outer F hc hs0 hs1 T hT k
  have hR0 : 0 ≤ R := le_trans (by norm_num : (0 : ℝ) ≤ 1) hR.le
  refine ⟨R, hR, ?_, ?_⟩
  · intro θ
    exact (hfar (greenPolar R θ)
      (greenPolar_norm_of_nonneg hR0 θ).ge).1
  · intro θ t ht0 ht1
    exact (hfar (greenPolar R θ)
      (greenPolar_norm_of_nonneg hR0 θ).ge).2 t ht0 ht1

end SpringerLean
