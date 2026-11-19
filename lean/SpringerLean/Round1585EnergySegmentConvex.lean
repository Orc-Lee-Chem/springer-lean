import SpringerLean.Round1584EnergyConvexTransfer

namespace SpringerLean
set_option maxHeartbeats 1000000
noncomputable section

/-- Values of the three piecewise affine multipliers at one time. -/
structure EnergyMultiplierValue where
  t : ℝ
  chi : ℝ
  f : ℝ
  sigma : ℝ

def coeffQ (v : EnergyMultiplierValue) (fp sp : ℝ) : ℝ :=
  2 * max 0 v.f + 2 * |v.f + v.t * fp| + v.t * |sp| + v.sigma

def coeffP (v : EnergyMultiplierValue) (fp sp : ℝ) : ℝ :=
  |v.f + v.t * fp| + v.t * |sp| / 2 + v.sigma

/-- The paper's three multiplier coefficients, with the positive reciprocal
scales left as independent parameters. This avoids division during convexity. -/
def energyMultiplierA (alpha fp sp : ℝ) (v : EnergyMultiplierValue) : ℝ :=
  v.chi + fp - |sp| / 2 - alpha * coeffQ v fp sp

def energyMultiplierB (alpha gamma b cp fp sp : ℝ)
    (v : EnergyMultiplierValue) : ℝ :=
  |v.chi - v.sigma| + |2*v.f-b*cp| + gamma*v.t*|cp|/2 +
    alpha*coeffP v fp sp

def energyMultiplierD (gamma K cp : ℝ) (v : EnergyMultiplierValue) : ℝ :=
  gamma*(K*v.chi+v.t*|cp|)/4

/-- On any affine cell, the exact multiplier quadratic is convex as a
function of the time parameter, for every nonnegative slope ratio. -/
theorem energyMultiplierQuadratic_segment_le
    {v₀ v₁ v : EnergyMultiplierValue}
    {lam alpha gamma K b cp fp sp s : ℝ}
    (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1)
    (halpha : 0 ≤ alpha) (hgamma : 0 ≤ gamma) (hs : 0 ≤ s)
    (ht : v.t = (1-lam)*v₀.t+lam*v₁.t)
    (hchi : v.chi = (1-lam)*v₀.chi+lam*v₁.chi)
    (hf : v.f = (1-lam)*v₀.f+lam*v₁.f)
    (hsigma : v.sigma = (1-lam)*v₀.sigma+lam*v₁.sigma) :
    signedEnergyQuadratic
        (energyMultiplierA alpha fp sp v)
        (energyMultiplierB alpha gamma b cp fp sp v)
        (energyMultiplierD gamma K cp v) s ≤
      (1-lam)*signedEnergyQuadratic
        (energyMultiplierA alpha fp sp v₀)
        (energyMultiplierB alpha gamma b cp fp sp v₀)
        (energyMultiplierD gamma K cp v₀) s +
      lam*signedEnergyQuadratic
        (energyMultiplierA alpha fp sp v₁)
        (energyMultiplierB alpha gamma b cp fp sp v₁)
        (energyMultiplierD gamma K cp v₁) s := by
  have hh : v.f+v.t*fp = (1-lam)*(v₀.f+v₀.t*fp)+lam*(v₁.f+v₁.t*fp) := by
    rw [hf, ht]
    ring
  have hfp := max_zero_affine_le hlam₀ hlam₁ hf
  have hhab := abs_affine_le hlam₀ hlam₁ hh
  rw [ht] at hhab
  have hcs : v.chi-v.sigma = (1-lam)*(v₀.chi-v₀.sigma)+
      lam*(v₁.chi-v₁.sigma) := by rw [hchi, hsigma]; ring
  have hfa : 2*v.f-b*cp = (1-lam)*(2*v₀.f-b*cp)+
      lam*(2*v₁.f-b*cp) := by rw [hf]; ring
  have hcsab := abs_affine_le hlam₀ hlam₁ hcs
  have hfab := abs_affine_le hlam₀ hlam₁ hfa
  have hQ : coeffQ v fp sp ≤
      (1-lam)*coeffQ v₀ fp sp+lam*coeffQ v₁ fp sp := by
    dsimp [coeffQ]
    rw [ht, hsigma]
    nlinarith
  have hP : coeffP v fp sp ≤
      (1-lam)*coeffP v₀ fp sp+lam*coeffP v₁ fp sp := by
    dsimp [coeffP]
    rw [ht, hsigma]
    nlinarith
  have hA : (1-lam)*energyMultiplierA alpha fp sp v₀+
      lam*energyMultiplierA alpha fp sp v₁ ≤
      energyMultiplierA alpha fp sp v := by
    have hQw := mul_le_mul_of_nonneg_left hQ halpha
    dsimp [energyMultiplierA]
    rw [hchi]
    nlinarith
  have hB : energyMultiplierB alpha gamma b cp fp sp v ≤
      (1-lam)*energyMultiplierB alpha gamma b cp fp sp v₀+
      lam*energyMultiplierB alpha gamma b cp fp sp v₁ := by
    have hPw := mul_le_mul_of_nonneg_left hP halpha
    have hgam := mul_nonneg hgamma (abs_nonneg cp)
    dsimp [energyMultiplierB]
    rw [ht]
    nlinarith
  have hD : energyMultiplierD gamma K cp v =
      (1-lam)*energyMultiplierD gamma K cp v₀+
      lam*energyMultiplierD gamma K cp v₁ := by
    dsimp [energyMultiplierD]
    rw [ht, hchi]
    ring
  calc
    signedEnergyQuadratic
        (energyMultiplierA alpha fp sp v)
        (energyMultiplierB alpha gamma b cp fp sp v)
        (energyMultiplierD gamma K cp v) s ≤
      signedEnergyQuadratic
        ((1-lam)*energyMultiplierA alpha fp sp v₀+
          lam*energyMultiplierA alpha fp sp v₁)
        ((1-lam)*energyMultiplierB alpha gamma b cp fp sp v₀+
          lam*energyMultiplierB alpha gamma b cp fp sp v₁)
        ((1-lam)*energyMultiplierD gamma K cp v₀+
          lam*energyMultiplierD gamma K cp v₁) s :=
        signedEnergyQuadratic_le_of_coefficient_envelope
          hA (le_of_eq hD) hB hs (le_refl _)
    _ = _ := by dsimp [signedEnergyQuadratic]; ring

end
end SpringerLean

#print axioms SpringerLean.energyMultiplierQuadratic_segment_le
