import SpringerLean.Round1439AffineCurvatureTangent

namespace SpringerLean
set_option maxHeartbeats 100000

noncomputable def movingArcCubicQ (B s₀ s : ℝ) : ℝ :=
  (1+B*s₀)*s^2/2-B*s^3/6

theorem movingArcCubicQ_hasDerivAt (B s₀ s : ℝ) :
    HasDerivAt (movingArcCubicQ B s₀)
      ((1+B*s₀)*s-B*s^2/2) s := by
  have hsq := ((hasDerivAt_id s).pow 2).const_mul ((1+B*s₀)/2)
  have hcube := ((hasDerivAt_id s).pow 3).const_mul (B/6)
  have hh := hsq.sub hcube
  convert hh using 1
  · funext x; dsimp [movingArcCubicQ]; ring
  · simp only [id_eq, pow_one,mul_one]
    ring

theorem movingArcCubicQ_deriv (B s₀ s : ℝ) :
    deriv (movingArcCubicQ B s₀) s =
      (1+B*s₀)*s-B*s^2/2 :=
  (movingArcCubicQ_hasDerivAt B s₀ s).deriv

theorem movingArcCubicQ_second_deriv (B s₀ s : ℝ) :
    deriv (deriv (movingArcCubicQ B s₀)) s =
      1+B*(s₀-s) := by
  have hformula : deriv (movingArcCubicQ B s₀) =
      fun x : ℝ => (1+B*s₀)*x-B*x^2/2 := by
    funext x
    exact movingArcCubicQ_deriv B s₀ x
  rw [hformula]
  have hlinear := (hasDerivAt_id s).const_mul (1+B*s₀)
  have hsq := ((hasDerivAt_id s).pow 2).const_mul (B/2)
  have hh := hlinear.sub hsq
  convert hh.deriv using 1
  · congr 1
    funext x
    dsimp
    ring
  · dsimp
    ring

theorem movingArcCubicQ_zero (B s₀ : ℝ) :
    movingArcCubicQ B s₀ 0 = 0 := by
  simp [movingArcCubicQ]

end SpringerLean

#print axioms SpringerLean.movingArcCubicQ_second_deriv
