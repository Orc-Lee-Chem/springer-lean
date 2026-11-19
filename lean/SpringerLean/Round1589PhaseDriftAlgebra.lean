import SpringerLean.Round1588EnergyAllTimeQuadratic

namespace SpringerLean

/-- The algebraic core of the drift PDE. Here `A` stands for
`beta * H^(k-2)`, `c` for the antiholomorphic derivative of `H`,
and the two terms on the right are the horizontal and vertical
components of `H · grad U`, after dividing by `k`. -/
theorem phase_drift_complex_algebra (H A c : ℂ) :
    Complex.normSq H * (A*c).im + (A*H^2).im =
      H.re * (A*H*(1+c)).im +
      H.im * (A*H*(Complex.I*(1-c))).im := by
  rcases H with ⟨x,y⟩
  rcases A with ⟨u,v⟩
  rcases c with ⟨p,q⟩
  simp [Complex.normSq_apply, Complex.mul_im, Complex.mul_re,
    Complex.add_im, Complex.add_re, Complex.sub_im, Complex.sub_re,
    pow_two]
  ring

/-- The no-division drift identity with its exact k-dependent factors,
assuming the Laplacian and gradient coordinates have the displayed
analytic forms. It remains valid at H=0. -/
theorem phase_drift_power_algebra
    (k : ℕ) (hk : 2 ≤ k) (H beta c : ℂ) :
    Complex.normSq H *
        (4*(k:ℝ)*((k:ℝ)-1)*(beta*H^(k-2)*c).im) +
      4*(k:ℝ)*((k:ℝ)-1)*(beta*H^k).im =
    4*((k:ℝ)-1) *
      (H.re * ((k:ℝ)*(beta*H^(k-1)*(1+c)).im) +
       H.im * ((k:ℝ)*(beta*H^(k-1)*
         (Complex.I*(1-c))).im)) := by
  have hp₁ : (beta*H^(k-2))*H = beta*H^(k-1) := by
    calc
      (beta*H^(k-2))*H = beta*(H^(k-2)*H) := by ring
      _ = beta*H^((k-2)+1) := by rw [pow_add, pow_one]
      _ = beta*H^(k-1) := by
        have hidx : k-2+1=k-1 := by omega
        rw [hidx]
  have hp₂ : (beta*H^(k-2))*H^2 = beta*H^k := by
    calc
      (beta*H^(k-2))*H^2 = beta*(H^(k-2)*H^2) := by ring
      _ = beta*H^((k-2)+2) := by rw [pow_add]
      _ = beta*H^k := by
        have hidx : k-2+2=k := by omega
        rw [hidx]
  have h := phase_drift_complex_algebra H (beta*H^(k-2)) c
  rw [hp₁, hp₂] at h
  calc
    _ = 4*(k:ℝ)*((k:ℝ)-1) *
        (Complex.normSq H * (beta*H^(k-2)*c).im +
          (beta*H^k).im) := by ring
    _ = 4*(k:ℝ)*((k:ℝ)-1) *
        (H.re * (beta*H^(k-1)*(1+c)).im +
         H.im * (beta*H^(k-1)*(Complex.I*(1-c))).im) := by rw [h]
    _ = _ := by ring

end SpringerLean

#print axioms SpringerLean.phase_drift_complex_algebra
#print axioms SpringerLean.phase_drift_power_algebra
