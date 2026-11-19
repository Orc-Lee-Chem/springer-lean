import SpringerLean.Rigidity

open scoped Topology

namespace SpringerLean

/-- The actual second-order remainder at infinity, defined by two analytic
difference quotients rather than by a proposed coefficient formula. -/
noncomputable def exteriorSecondTail (F : ℂ → ℂ) : ℂ → ℂ :=
  dslope (dslope (exteriorForwardGerm F) 0) 0

theorem exteriorSecondTail_analyticAt (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) :
    AnalyticAt ℂ (exteriorSecondTail F) 0 :=
  analyticAt_dslope_zero _
    (analyticAt_dslope_zero _ hc.2.2)

/-- Exact second-order decomposition of the actual forward correction. -/
theorem exteriorForwardGerm_eq_first_add_secondTail
    (F : ℂ → ℂ) (u : ℂ) :
    exteriorForwardGerm F u =
      exteriorForwardCoeff F 1 * u + u ^ 2 * exteriorSecondTail F u := by
  let f := exteriorForwardGerm F
  let q := dslope f 0
  have hf0 : f 0 = 0 := exteriorForwardGerm_zero F
  have hq0 : q 0 = exteriorForwardCoeff F 1 := by
    simp [q, f, dslope_same, exteriorForwardCoeff,
      iteratedDeriv_succ']
  have h1 := analytic_dslope_decomposition f u
  have h2 := analytic_dslope_decomposition q u
  dsimp [exteriorSecondTail]
  rw [hf0] at h1
  rw [hq0] at h2
  change f u = 0 + u * q u at h1
  rw [h2] at h1
  calc
    exteriorForwardGerm F u =
        u * (exteriorForwardCoeff F 1 + u * exteriorSecondTail F u) := by
          simpa [f, q, exteriorSecondTail] using h1
    _ = _ := by
      dsimp [exteriorSecondTail]
      ring

/-- The second-order remainder has a locally uniform norm bound. -/
theorem exteriorSecondTail_eventually_norm_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∀ᶠ u in 𝓝 (0 : ℂ),
      ‖exteriorSecondTail F u‖ ≤ ‖exteriorSecondTail F 0‖ + 1 := by
  have hcont := (exteriorSecondTail_analyticAt F hc).continuousAt.norm
  have hstrict : ‖exteriorSecondTail F 0‖ <
      ‖exteriorSecondTail F 0‖ + 1 := by linarith
  have hopen : IsOpen {x : ℝ | x < ‖exteriorSecondTail F 0‖ + 1} :=
    isOpen_lt continuous_id continuous_const
  have hevent := hcont.eventually (hopen.mem_nhds hstrict)
  filter_upwards [hevent] with u hu
  exact hu.le

/-- A uniform O(|u|²) estimate for the actual normalized correction. -/
theorem exteriorForwardGerm_second_order_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∀ᶠ u in 𝓝 (0 : ℂ),
      ‖exteriorForwardGerm F u - exteriorForwardCoeff F 1 * u‖ ≤
        (‖exteriorSecondTail F 0‖ + 1) * ‖u‖ ^ 2 := by
  filter_upwards [exteriorSecondTail_eventually_norm_bound F hc] with u hu
  rw [exteriorForwardGerm_eq_first_add_secondTail F u, add_sub_cancel_left]
  rw [norm_mul, norm_pow]
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_right hu (sq_nonneg ‖u‖))

end SpringerLean