import SpringerLean.Round2006OddStarUniformRegularDomain

namespace SpringerLean
open scoped Topology

theorem oddStarBoundaryFactor_differentiableAt
    (ζ : ℂ) (t : ℝ) (ht : |t| < 1)
    (hden : ((Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I) * ζ -
      (t : ℂ) * Complex.I ≠ 0) :
    DifferentiableAt ℝ (oddStarBoundaryFactor ζ) t := by
  have hbase : 0 < 1 - t ^ 2 := by
    have hlt := (abs_lt.mp ht)
    nlinarith
  have hsqrt : DifferentiableAt ℝ
      (fun x : ℝ => Real.sqrt (1 - x ^ 2)) t := by
    apply (Real.hasDerivAt_sqrt (by linarith : 1 - t ^ 2 ≠ 0)).differentiableAt.comp t
    fun_prop
  change DifferentiableAt ℝ (fun x : ℝ =>
    (((Real.sqrt (1 - x ^ 2) : ℂ) - (x : ℂ) * Complex.I) ^ 2 * ζ) /
      (((Real.sqrt (1 - x ^ 2) : ℂ) - (x : ℂ) * Complex.I) * ζ -
        (x : ℂ) * Complex.I)) t
  fun_prop (discharger := assumption)

theorem oddStarMovingBoundaryPoint_differentiableAt
    (m : ℕ) (r θ t : ℝ) (ht : |t| < 1)
    (hden : ((Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I) *
      Complex.exp ((θ : ℂ) * Complex.I) -
      (t : ℂ) * Complex.I ≠ 0)
    (hslit : oddStarBoundaryFactor
      (Complex.exp ((θ : ℂ) * Complex.I)) t ∈ Complex.slitPlane) :
    DifferentiableAt ℝ (oddStarMovingBoundaryPoint m r θ) t := by
  have hfactor := oddStarBoundaryFactor_differentiableAt
    (Complex.exp ((θ : ℂ) * Complex.I)) t ht hden
  have hlog : DifferentiableAt ℝ
      (fun x : ℝ => Complex.log
        (oddStarBoundaryFactor (Complex.exp ((θ : ℂ) * Complex.I)) x)) t :=
    (hfactor.hasDerivAt.clog_real hslit).differentiableAt
  change DifferentiableAt ℝ (fun x : ℝ =>
    (r : ℂ) * Complex.exp
      (((m : ℂ)⁻¹) * Complex.log
        (oddStarBoundaryFactor (Complex.exp ((θ : ℂ) * Complex.I)) x))) t
  fun_prop

theorem oddStarTipRadius_differentiableAt
    (m : ℕ) (t : ℝ) (ht : |t| < 1) :
    DifferentiableAt ℝ (oddStarTipRadius m) t := by
  have hbase : 0 < 1 - t ^ 2 := by
    have hlt := abs_lt.mp ht
    nlinarith
  have hsqrt : DifferentiableAt ℝ
      (fun x : ℝ => Real.sqrt (1 - x ^ 2)) t := by
    apply (Real.hasDerivAt_sqrt (by linarith : 1 - t ^ 2 ≠ 0)).differentiableAt.comp t
    fun_prop
  have houter : DifferentiableAt ℝ
      (fun x : ℝ => x ^ ((m : ℝ)⁻¹))
      (4 * Real.sqrt (1 - t ^ 2)) :=
    Real.differentiableAt_rpow_const_of_ne _ (by positivity)
  have hinner : DifferentiableAt ℝ
      (fun x : ℝ => 4 * Real.sqrt (1 - x ^ 2)) t := by
    fun_prop
  convert houter.comp t hinner using 1
  funext x
  rfl

theorem oddStarOppositeTipLogDistance_differentiableAt
    (m : ℕ) (θ t : ℝ) (ht : |t| < 1)
    (hden : ((Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I) *
      Complex.exp ((θ : ℂ) * Complex.I) -
      (t : ℂ) * Complex.I ≠ 0)
    (hslit : oddStarBoundaryFactor
      (Complex.exp ((θ : ℂ) * Complex.I)) t ∈ Complex.slitPlane)
    (hdist : oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t -
      (oddStarTipRadius m t : ℂ) *
        Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I) ≠ 0) :
    DifferentiableAt ℝ (oddStarOppositeTipLogDistance m θ) t := by
  have hZ := oddStarMovingBoundaryPoint_differentiableAt m
    (oddStarBoundaryRadius m θ) θ t ht hden hslit
  have hR := oddStarTipRadius_differentiableAt m t ht
  have hf : DifferentiableAt ℝ (fun x : ℝ =>
      oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ x -
      (oddStarTipRadius m x : ℂ) *
        Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)) t := by
    fun_prop
  have hnorm := hf.norm ℝ hdist
  have hlog :=
    (Real.differentiableAt_log (norm_ne_zero_iff.mpr hdist)).comp t hnorm
  convert hlog using 1
  funext x
  rfl

/-- A common parameter neighborhood makes every angular integrand
differentiable in the parameter. -/
theorem oddStarOppositeTipLogDistance_uniform_differentiable :
    ∀ (m : ℕ), 3 ≤ m →
    ∃ U : Set ℝ, U ∈ 𝓝 (0 : ℝ) ∧
      ∀ t ∈ U, ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        DifferentiableAt ℝ (oddStarOppositeTipLogDistance m θ) t := by
  intro m hm
  obtain ⟨U, hU, hreg⟩ := oddStarVariation_uniform_regular_domain m hm
  let V : Set ℝ := Set.Ioo (-1 : ℝ) 1
  have hV : V ∈ 𝓝 (0 : ℝ) := by
    apply IsOpen.mem_nhds isOpen_Ioo
    norm_num [V]
  refine ⟨U ∩ V, Filter.inter_mem hU hV, ?_⟩
  intro t ht θ hθ
  have hprops := hreg t ht.1 θ hθ
  have ht1 : |t| < 1 := by
    have htv : t ∈ V := ht.2
    simpa [V, abs_lt] using htv
  have hRpos := oddStarTipRadius_zero_pos m
  have hvec : oddStarMovingBoundaryPoint m
      (oddStarBoundaryRadius m θ) θ t -
      (oddStarTipRadius m t : ℂ) *
        Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I) ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at hprops
    linarith [hprops.1]
  exact oddStarOppositeTipLogDistance_differentiableAt m θ t ht1
    hprops.2.2 hprops.2.1 hvec

end SpringerLean

#print axioms SpringerLean.oddStarOppositeTipLogDistance_uniform_differentiable
