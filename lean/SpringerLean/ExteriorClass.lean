import SpringerLean.GeneralFirst

open scoped Topology

namespace SpringerLean

/-- The paper's centered exterior class: holomorphic and univalent on the open
exterior disk, with a convergent, constant-free Laurent correction at infinity.
The last condition is an analytic germ, equivalent below to a local convergent series. -/
def CenteredExteriorUnivalent (F : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ F exteriorDisk ∧
    Set.InjOn F exteriorDisk ∧
    AnalyticAt ℂ (exteriorForwardGerm F) 0

theorem exteriorForwardGerm_zero (F : ℂ → ℂ) :
    exteriorForwardGerm F 0 = 0 := by
  simp [exteriorForwardGerm]

theorem exteriorForwardGerm_punctured (F : ℂ → ℂ) {t : ℂ} (ht : t ≠ 0) :
    exteriorForwardGerm F t = F t⁻¹ - t⁻¹ := by
  simp [exteriorForwardGerm, ht]

theorem exteriorForwardCoeff_zero (F : ℂ → ℂ) :
    exteriorForwardCoeff F 0 = 0 := by
  simp [exteriorForwardCoeff, exteriorForwardGerm]

/-- The coefficients read by derivatives are the convergent Laurent coefficients. -/
theorem exteriorForwardGerm_hasSum_coeff (F : ℂ → ℂ)
    (hf : AnalyticAt ℂ (exteriorForwardGerm F) 0) :
    ∀ᶠ t in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => exteriorForwardCoeff F n * t ^ n)
        (exteriorForwardGerm F t) := by
  have hp := hf.hasFPowerSeriesAt
  have hs := hasFPowerSeriesAt_iff.mp hp
  filter_upwards [hs] with t ht
  simpa [FormalMultilinearSeries.coeff_ofScalars, exteriorForwardCoeff,
    smul_eq_mul, mul_comm] using ht

/-- An analytic normalized forward germ is exactly a convergent constant-free
Laurent correction in the local coordinate t=1/z. -/
theorem exteriorForward_analytic_iff_series (F : ℂ → ℂ) :
    AnalyticAt ℂ (exteriorForwardGerm F) 0 ↔
      ∃ b : ℕ → ℂ, b 0 = 0 ∧
        ∀ᶠ t in 𝓝 (0 : ℂ),
          HasSum (fun n : ℕ => b n * t ^ n) (exteriorForwardGerm F t) := by
  constructor
  · intro hf
    exact ⟨exteriorForwardCoeff F, exteriorForwardCoeff_zero F,
      exteriorForwardGerm_hasSum_coeff F hf⟩
  · rintro ⟨b, hb0, hs⟩
    refine ⟨FormalMultilinearSeries.ofScalars ℂ b, ?_⟩
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [hs] with t ht
    simpa [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using ht

theorem slitMap_centeredExteriorUnivalent (a : ℂ) (ha : ‖a‖ = 1) :
    CenteredExteriorUnivalent (slitMap a) := by
  refine ⟨?_, slitMap_injOn a ha, ?_⟩
  · intro z hz
    exact (slitMap_analyticAt a z (exterior_ne_zero hz)).differentiableAt.differentiableWithinAt
  · have hfun : exteriorForwardGerm (slitMap a) = fun t : ℂ => a * t := by
      funext t
      by_cases ht : t = 0
      · simp [exteriorForwardGerm, ht]
      · simp [exteriorForwardGerm, slitMap, ht, div_eq_mul_inv]
    rw [hfun]
    fun_prop

/-- The general actual-inverse coefficient interface specializes definitionally
to the derivative coefficients already proved for the rotated slit. -/
theorem exteriorInverseCoeff_slitMap (a : ℂ) (n : ℕ) :
    exteriorInverseCoeff (slitMap a) n = slitTaylorCoeff a n := by
  rfl

/-- Any convergent forward Laurent coefficient sequence agrees termwise with
the independent derivative-based reading of the actual F. -/
theorem exteriorForwardCoeff_eq_of_hasSum (F : ℂ → ℂ) (b : ℕ → ℂ)
    (hs : ∀ᶠ t in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => b n * t ^ n) (exteriorForwardGerm F t))
    (n : ℕ) :
    exteriorForwardCoeff F n = b n := by
  have hb : HasFPowerSeriesAt (exteriorForwardGerm F)
      (FormalMultilinearSeries.ofScalars ℂ b) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [hs] with t ht
    simpa [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using ht
  have hp := hb.analyticAt.hasFPowerSeriesAt
  have heq := hp.eq_formalMultilinearSeries hb
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
  simpa [exteriorForwardCoeff, FormalMultilinearSeries.coeff_ofScalars] using hc
/-- The sharpness witness is now available through the general actual-F interface. -/
theorem slitMap_exteriorInverseCoeff_sharp_witness (a : ℂ) (ha : ‖a‖ = 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖exteriorInverseCoeff (slitMap a) (2 * k - 1)‖ =
      (catalan (k - 1) : ℝ) := by
  rw [exteriorInverseCoeff_slitMap]
  exact slitTaylorCoeff_sharp_witness a ha k hk
end SpringerLean