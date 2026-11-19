import SpringerLean.Round601TwoOmittedRootMidpoint
import SpringerLean.Round90FaberCombination

open scoped Topology

namespace SpringerLean
set_option Elab.async false

noncomputable def exteriorReciprocalGerm (V : ℂ → ℂ) (u : ℂ) : ℂ :=
  u / (1 + u * exteriorForwardGerm V u)

noncomputable def exteriorReciprocalCoeff (V : ℂ → ℂ) (n : ℕ) : ℂ :=
  actualTaylorCoeff (exteriorReciprocalGerm V) n

theorem exteriorReciprocalGerm_analyticAt (V : ℂ → ℂ)
    (hV : CenteredExteriorUnivalent V) : AnalyticAt ℂ (exteriorReciprocalGerm V) 0 :=
  analyticAt_id.div (analyticAt_const.add (analyticAt_id.mul hV.2.2)) (by simp)

theorem exteriorReciprocalGerm_eq_inv (V : ℂ → ℂ)
    {u : ℂ} (hu : u ≠ 0) (hV : V u⁻¹ ≠ 0) :
    exteriorReciprocalGerm V u = (V u⁻¹)⁻¹ := by
  rw [exteriorReciprocalGerm, exteriorForwardGerm_punctured _ hu]
  have hd : 1 + u * (V u⁻¹ - u⁻¹) = u * V u⁻¹ := by field_simp; ring
  rw [hd]
  field_simp [hu, hV]

theorem exteriorRootMidpoint_forwardCoeff
    (H J : ℂ → ℂ) (hH : CenteredExteriorUnivalent H)
    (hJ : CenteredExteriorUnivalent J) (n : ℕ) :
    exteriorForwardCoeff (exteriorRootMidpoint H J) n =
      (exteriorForwardCoeff H n + exteriorForwardCoeff J n) / 2 := by
  change actualTaylorCoeff _ n = _
  rw [exteriorRootMidpoint_forwardGerm]
  have he : (fun u => (exteriorForwardGerm H u + exteriorForwardGerm J u) / 2) =
      (fun u => (1 / 2 : ℂ) * (exteriorForwardGerm H u + exteriorForwardGerm J u)) := by
    funext u
    ring
  rw [he, actualTaylorCoeff_const_mul_analytic,
    actualTaylorCoeff_add_analytic _ _ hH.2.2 hJ.2.2]
  simp only [exteriorForwardCoeff, actualTaylorCoeff]
  ring

theorem exteriorRootMidpoint_reciprocal_coefficients
    (H J : ℂ → ℂ) (hH : CenteredExteriorUnivalent H)
    (hJ : CenteredExteriorUnivalent J) (q : ℂ) (hq : q ≠ 0)
    (hs : ∀ z ∈ exteriorDisk, H z ^ 2 - J z ^ 2 = 4 * q) (n : ℕ) :
    exteriorForwardCoeff H n = exteriorForwardCoeff (exteriorRootMidpoint H J) n +
        q * exteriorReciprocalCoeff (exteriorRootMidpoint H J) n ∧
    exteriorForwardCoeff J n = exteriorForwardCoeff (exteriorRootMidpoint H J) n -
        q * exteriorReciprocalCoeff (exteriorRootMidpoint H J) n := by
  let V := exteriorRootMidpoint H J
  have hV := exteriorRootMidpoint_centeredExteriorUnivalent H J hH hJ q hq hs
  have hnear : exteriorForwardGerm H =ᶠ[𝓝 (0 : ℂ)]
      fun u => exteriorForwardGerm V u + q * exteriorReciprocalGerm V u := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with u hu
    by_cases hu0 : u = 0
    · simp [hu0, exteriorReciprocalGerm, exteriorForwardGerm_zero]
    have hu1 : ‖u‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hu
    have hue : u⁻¹ ∈ exteriorDisk := by
      change 1 < ‖u⁻¹‖
      rw [norm_inv]
      exact one_lt_inv₀ (norm_pos_iff.mpr hu0) |>.mpr hu1
    obtain ⟨hnz, hrecover⟩ := exteriorRootMidpoint_recover_left H J q hq hs hue
    rw [exteriorReciprocalGerm_eq_inv V hu0 hnz,
      exteriorForwardGerm_punctured H hu0, exteriorForwardGerm_punctured V hu0]
    dsimp [V] at *
    rw [hrecover]
    ring
  have hcoef := actualTaylorCoeff_congr hnear n
  have hqR : AnalyticAt ℂ (fun u => q * exteriorReciprocalGerm V u) 0 :=
    analyticAt_const.mul (exteriorReciprocalGerm_analyticAt V hV)
  rw [actualTaylorCoeff_add_analytic (exteriorForwardGerm V)
    (fun u => q * exteriorReciprocalGerm V u) hV.2.2 hqR n,
    actualTaylorCoeff_const_mul_analytic] at hcoef
  change exteriorForwardCoeff H n = exteriorForwardCoeff V n +
    q * exteriorReciprocalCoeff V n at hcoef
  refine ⟨hcoef, ?_⟩
  have hm := exteriorRootMidpoint_forwardCoeff H J hH hJ n
  change exteriorForwardCoeff V n = _ at hm
  change exteriorForwardCoeff J n = exteriorForwardCoeff V n -
    q * exteriorReciprocalCoeff V n
  linear_combination -2 * hm - hcoef

/-- Finite parallelogram budget for the actual reciprocal of the univalent
midpoint. No area identity for an image of the midpoint is assumed. -/
theorem exteriorRootMidpoint_finite_reciprocal_energy
    (H J : ℂ → ℂ) (hH : CenteredExteriorUnivalent H)
    (hJ : CenteredExteriorUnivalent J) (q : ℂ) (hq : q ≠ 0)
    (hs : ∀ z ∈ exteriorDisk, H z ^ 2 - J z ^ 2 = 4 * q) (N : ℕ) :
    (∑ j ∈ Finset.Icc 1 N,
      (j : ℝ) * ‖exteriorForwardCoeff (exteriorRootMidpoint H J) j‖ ^ 2) +
      ‖q‖ ^ 2 * (∑ j ∈ Finset.Icc 1 N,
        (j : ℝ) * ‖exteriorReciprocalCoeff (exteriorRootMidpoint H J) j‖ ^ 2) ≤ 1 := by
  have hterm (j : ℕ) :
      ‖exteriorForwardCoeff H j‖ ^ 2 + ‖exteriorForwardCoeff J j‖ ^ 2 =
        2 * (‖exteriorForwardCoeff (exteriorRootMidpoint H J) j‖ ^ 2 +
          ‖q‖ ^ 2 * ‖exteriorReciprocalCoeff (exteriorRootMidpoint H J) j‖ ^ 2) := by
    obtain ⟨hh,hj⟩ := exteriorRootMidpoint_reciprocal_coefficients H J hH hJ q hq hs j
    rw [hh, hj]
    simpa only [norm_mul, mul_pow] using parallelogram_law_with_norm ℂ
      (exteriorForwardCoeff (exteriorRootMidpoint H J) j)
      (q * exteriorReciprocalCoeff (exteriorRootMidpoint H J) j)
  have hsum :
      (∑ j ∈ Finset.Icc 1 N, (j : ℝ) * ‖exteriorForwardCoeff H j‖ ^ 2) +
      (∑ j ∈ Finset.Icc 1 N, (j : ℝ) * ‖exteriorForwardCoeff J j‖ ^ 2) =
      2 * ((∑ j ∈ Finset.Icc 1 N,
        (j : ℝ) * ‖exteriorForwardCoeff (exteriorRootMidpoint H J) j‖ ^ 2) +
        ‖q‖ ^ 2 * (∑ j ∈ Finset.Icc 1 N,
          (j : ℝ) * ‖exteriorReciprocalCoeff (exteriorRootMidpoint H J) j‖ ^ 2)) := by
    calc
      _ = ∑ j ∈ Finset.Icc 1 N,
          ((j : ℝ) * ‖exteriorForwardCoeff H j‖ ^ 2 +
           (j : ℝ) * ‖exteriorForwardCoeff J j‖ ^ 2) := by rw [Finset.sum_add_distrib]
      _ = ∑ j ∈ Finset.Icc 1 N,
          2 * ((j : ℝ) * ‖exteriorForwardCoeff (exteriorRootMidpoint H J) j‖ ^ 2 +
            ‖q‖ ^ 2 * ((j : ℝ) * ‖exteriorReciprocalCoeff (exteriorRootMidpoint H J) j‖ ^ 2)) := by
        apply Finset.sum_congr rfl
        intro j hj
        linear_combination (j : ℝ) * hterm j
      _ = _ := by simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  have hh := exteriorForwardCoeff_finite_area H hH N
  have hj := exteriorForwardCoeff_finite_area J hJ N
  nlinarith

end SpringerLean
