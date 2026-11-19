import SpringerLean.Round10Primitive

namespace SpringerLean

/-- The polar parameter used by all four Green rectangles. -/
noncomputable def greenPolar (r θ : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

@[simp] theorem greenPolar_zero (r : ℝ) : greenPolar r 0 = (r : ℂ) := by
  simp [greenPolar]

@[simp] theorem greenPolar_two_pi (r : ℝ) :
    greenPolar r (2 * Real.pi) = (r : ℂ) := by
  simp [greenPolar, Complex.ofReal_mul]

theorem greenPolar_norm_of_nonneg {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖greenPolar r θ‖ = r := by
  rw [greenPolar, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr]
  simp

/-- Every composition with the polar parameter has exactly matching
angular endpoints, as an equality of radial functions. -/
theorem greenPolar_endpoint_functions (W : ℂ → ℂ) :
    (fun r : ℝ => W (greenPolar r (2 * Real.pi))) =
      (fun r : ℝ => W (greenPolar r 0)) := by
  funext r
  simp

/-- The radial derivatives at the two angular endpoints match. This is the
periodicity premise needed by `periodic_rectangle_flux` for the disk,
annulus and identity maps. -/
theorem greenPolar_endpoint_radial_deriv
    (W : ℂ → ℂ) (r : ℝ) :
    deriv (fun t : ℝ => W (greenPolar t (2 * Real.pi))) r =
      deriv (fun t : ℝ => W (greenPolar t 0)) r := by
  rw [greenPolar_endpoint_functions]

/-- The straight homotopy between the standard outer circle and the actual
regularized outer curve also has matching angular endpoints for every time. -/
theorem regularOuterHomotopy_endpoint_functions
    (F : ℂ → ℂ) (s R : ℝ) :
    (fun t : ℝ => greenPolar R (2 * Real.pi) +
      (t : ℂ) * (rescaleExterior s F (greenPolar R (2 * Real.pi)) -
        greenPolar R (2 * Real.pi))) =
    (fun t : ℝ => greenPolar R 0 +
      (t : ℂ) * (rescaleExterior s F (greenPolar R 0) -
        greenPolar R 0)) := by
  simp

theorem regularOuterHomotopy_endpoint_radial_deriv
    (F : ℂ → ℂ) (s R t : ℝ) :
    deriv (fun q : ℝ => greenPolar R (2 * Real.pi) +
      (q : ℂ) * (rescaleExterior s F (greenPolar R (2 * Real.pi)) -
        greenPolar R (2 * Real.pi))) t =
    deriv (fun q : ℝ => greenPolar R 0 +
      (q : ℂ) * (rescaleExterior s F (greenPolar R 0) -
        greenPolar R 0)) t := by
  rw [regularOuterHomotopy_endpoint_functions]

end SpringerLean
