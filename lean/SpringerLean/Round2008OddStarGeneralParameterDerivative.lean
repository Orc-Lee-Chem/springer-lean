import SpringerLean.Round2007OddStarUniformDifferentiability

namespace SpringerLean
open scoped RealInnerProductSpace

noncomputable def oddStarAlpha (t : ℝ) : ℂ :=
  (Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I

noncomputable def oddStarAlphaSlope (t : ℝ) : ℂ :=
  (((-2 * t) / (2 * Real.sqrt (1 - t ^ 2))) : ℂ) - Complex.I

theorem oddStarAlpha_hasDerivAt
    (t : ℝ) (ht : |t| < 1) :
    HasDerivAt oddStarAlpha (oddStarAlphaSlope t) t := by
  have hbasepos : 0 < 1 - t ^ 2 := by
    have hlt := abs_lt.mp ht
    nlinarith
  have hbase : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * t) t := by
    convert (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2) using 1 <;>
      norm_num <;> (funext x; rfl)
  have hroot : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2))
      ((-2 * t) / (2 * Real.sqrt (1 - t ^ 2))) t := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hbasepos)).comp t hbase using 1
    · funext x; rfl
    · field_simp
  have hcoe : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := by
    have h : HasDerivAt (Complex.ofRealCLM : ℝ → ℂ) 1 t := by
      simpa using (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).hasDerivAt
    convert h using 1
    funext x
    exact (Complex.ofRealCLM_apply x).symm
  have hrootC := hroot.ofReal_comp
  convert hrootC.sub (hcoe.mul_const Complex.I) using 1
  · funext x
    rfl
  · simp [oddStarAlphaSlope]

noncomputable def oddStarBoundaryDenominator (ζ : ℂ) (t : ℝ) : ℂ :=
  oddStarAlpha t * ζ - (t : ℂ) * Complex.I

noncomputable def oddStarBoundaryFactorSlope (ζ : ℂ) (t : ℝ) : ℂ :=
  ((2 * oddStarAlpha t * oddStarAlphaSlope t * ζ) *
      oddStarBoundaryDenominator ζ t -
    (oddStarAlpha t ^ 2 * ζ) *
      (oddStarAlphaSlope t * ζ - Complex.I)) /
    oddStarBoundaryDenominator ζ t ^ 2

theorem oddStarBoundaryFactor_hasDerivAt_general
    (ζ : ℂ) (t : ℝ) (ht : |t| < 1)
    (hden : oddStarBoundaryDenominator ζ t ≠ 0) :
    HasDerivAt (oddStarBoundaryFactor ζ)
      (oddStarBoundaryFactorSlope ζ t) t := by
  have hα := oddStarAlpha_hasDerivAt t ht
  have hcoe : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := by
    have h : HasDerivAt (Complex.ofRealCLM : ℝ → ℂ) 1 t := by
      simpa using (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).hasDerivAt
    convert h using 1
    funext x
    exact (Complex.ofRealCLM_apply x).symm
  have hnum := (hα.pow 2).mul_const ζ
  have hdenDeriv := (hα.mul_const ζ).sub (hcoe.mul_const Complex.I)
  have hquot := hnum.div hdenDeriv hden
  convert hquot using 1
  · funext x
    rfl
  · simp [oddStarBoundaryFactorSlope, oddStarBoundaryDenominator,
      oddStarAlpha, oddStarAlphaSlope]

noncomputable def oddStarBoundaryLogSlope (ζ : ℂ) (t : ℝ) : ℂ :=
  oddStarBoundaryFactorSlope ζ t / oddStarBoundaryFactor ζ t

theorem oddStarBoundaryLog_hasDerivAt_general
    (ζ : ℂ) (t : ℝ) (ht : |t| < 1)
    (hden : oddStarBoundaryDenominator ζ t ≠ 0)
    (hslit : oddStarBoundaryFactor ζ t ∈ Complex.slitPlane) :
    HasDerivAt (fun x : ℝ => Complex.log (oddStarBoundaryFactor ζ x))
      (oddStarBoundaryLogSlope ζ t) t := by
  simpa [oddStarBoundaryLogSlope] using
    (oddStarBoundaryFactor_hasDerivAt_general ζ t ht hden).clog_real hslit

noncomputable def oddStarMovingBoundaryPointSlope
    (m : ℕ) (r θ t : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp
    (((m : ℂ)⁻¹) * Complex.log
      (oddStarBoundaryFactor (Complex.exp ((θ : ℂ) * Complex.I)) t)) *
    (m : ℂ)⁻¹ *
    oddStarBoundaryLogSlope (Complex.exp ((θ : ℂ) * Complex.I)) t

theorem oddStarMovingBoundaryPoint_hasDerivAt_general
    (m : ℕ) (r θ t : ℝ) (ht : |t| < 1)
    (hden : oddStarBoundaryDenominator
      (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0)
    (hslit : oddStarBoundaryFactor
      (Complex.exp ((θ : ℂ) * Complex.I)) t ∈ Complex.slitPlane) :
    HasDerivAt (oddStarMovingBoundaryPoint m r θ)
      (oddStarMovingBoundaryPointSlope m r θ t) t := by
  have hlog := oddStarBoundaryLog_hasDerivAt_general _ t ht hden hslit
  have hscaled := hlog.const_mul (m : ℂ)⁻¹
  have hexp := hscaled.cexp
  have hpoint := hexp.const_mul (r : ℂ)
  convert hpoint using 1
  · funext x
    rfl
  · simp [oddStarMovingBoundaryPointSlope]
    ring

noncomputable def oddStarTipRadiusSlope (m : ℕ) (t : ℝ) : ℝ :=
  ((m : ℝ)⁻¹) *
    (4 * Real.sqrt (1 - t ^ 2)) ^ ((m : ℝ)⁻¹ - 1) *
      (4 * ((-2 * t) / (2 * Real.sqrt (1 - t ^ 2))))

theorem oddStarTipRadius_hasDerivAt_general
    (m : ℕ) (t : ℝ) (ht : |t| < 1) :
    HasDerivAt (oddStarTipRadius m) (oddStarTipRadiusSlope m t) t := by
  have hbasepos : 0 < 1 - t ^ 2 := by
    have hlt := abs_lt.mp ht
    nlinarith
  have hbase : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * t) t := by
    convert (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2) using 1 <;>
      norm_num <;> (funext x; rfl)
  have hroot : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2))
      ((-2 * t) / (2 * Real.sqrt (1 - t ^ 2))) t := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hbasepos)).comp t hbase using 1
    · funext x; rfl
    · field_simp
  have hinner : HasDerivAt
      (fun x : ℝ => 4 * Real.sqrt (1 - x ^ 2))
      (4 * ((-2 * t) / (2 * Real.sqrt (1 - t ^ 2)))) t := by
    convert (hasDerivAt_const t (4 : ℝ)).mul hroot using 1 <;> simp
  have houter : HasDerivAt
      (fun x : ℝ => x ^ ((m : ℝ)⁻¹))
      (((m : ℝ)⁻¹) *
        (4 * Real.sqrt (1 - t ^ 2)) ^ ((m : ℝ)⁻¹ - 1))
      (4 * Real.sqrt (1 - t ^ 2)) :=
    Real.hasDerivAt_rpow_const (Or.inl (by positivity))
  convert houter.comp t hinner using 1
  · funext x
    rfl
  · simp [oddStarTipRadiusSlope]

theorem log_norm_hasDerivAt_at
    (f : ℝ → ℂ) (f' : ℂ) (t : ℝ) (hf : HasDerivAt f f' t)
    (h0 : f t ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log ‖f x‖)
      (⟪f t, f'⟫ / ‖f t‖ ^ 2) t := by
  have hsq : HasDerivAt (fun x : ℝ => ‖f x‖ ^ 2)
      (2 * ⟪f t, f'⟫) t := hf.norm_sq
  have hsqne : ‖f t‖ ^ 2 ≠ 0 := by
    simp [h0]
  have hlog := hsq.log hsqne
  have hhalf := hlog.const_mul ((1 / 2 : ℝ))
  convert hhalf using 1
  · funext x
    rw [Real.log_pow]
    ring
  · ring

noncomputable def oddStarOppositeTipLogSlope
    (m : ℕ) (θ t : ℝ) : ℝ :=
  let η : ℂ := Complex.exp
    (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)
  let f : ℂ := oddStarMovingBoundaryPoint m
      (oddStarBoundaryRadius m θ) θ t -
    (oddStarTipRadius m t : ℂ) * η
  let f' : ℂ := oddStarMovingBoundaryPointSlope m
      (oddStarBoundaryRadius m θ) θ t -
    (oddStarTipRadiusSlope m t : ℂ) * η
  ⟪f, f'⟫ / ‖f‖ ^ 2

theorem oddStarOppositeTipLogDistance_hasDerivAt_general
    (m : ℕ) (θ t : ℝ) (ht : |t| < 1)
    (hden : oddStarBoundaryDenominator
      (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0)
    (hslit : oddStarBoundaryFactor
      (Complex.exp ((θ : ℂ) * Complex.I)) t ∈ Complex.slitPlane)
    (hdist : oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t -
      (oddStarTipRadius m t : ℂ) *
        Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I) ≠ 0) :
    HasDerivAt (oddStarOppositeTipLogDistance m θ)
      (oddStarOppositeTipLogSlope m θ t) t := by
  let η : ℂ := Complex.exp
    (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)
  let f : ℝ → ℂ := fun x =>
    oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ x -
      (oddStarTipRadius m x : ℂ) * η
  have hZ := oddStarMovingBoundaryPoint_hasDerivAt_general m
    (oddStarBoundaryRadius m θ) θ t ht hden hslit
  have hR := (oddStarTipRadius_hasDerivAt_general m t ht).ofReal_comp
  have hf : HasDerivAt f
      (oddStarMovingBoundaryPointSlope m
        (oddStarBoundaryRadius m θ) θ t -
        (oddStarTipRadiusSlope m t : ℂ) * η) t := by
    convert hZ.sub (hR.mul_const η) using 1 <;> simp [f]
  convert log_norm_hasDerivAt_at f _ t hf hdist using 1
  · funext x
    rfl
  · rfl

end SpringerLean

#print axioms SpringerLean.oddStarOppositeTipLogDistance_hasDerivAt_general
