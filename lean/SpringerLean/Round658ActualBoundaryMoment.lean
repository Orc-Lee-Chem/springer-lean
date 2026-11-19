import SpringerLean.Round657TaylorCircleBound
import SpringerLean.RescaleGerm

namespace SpringerLean
set_option Elab.async false

/-- The actual inverse/residue coefficient controls the actual regularized
boundary moment with the exact factor n. No radial boundary values are used. -/
theorem rescaleExterior_inverseCoeff_mul_norm_le_boundary_moment
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ)*‖exteriorInverseCoeff (rescaleExterior s F) n‖ ≤
      Real.circleAverage (fun ζ => ‖rescaleExterior s F ζ‖^n) 0 1 := by
  let G := rescaleExterior s F
  have hG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  have hPhi : AnalyticOnNhd ℂ (exteriorPhi G) (Metric.ball (0 : ℂ) s⁻¹) := by
    intro u hu
    have hg := regularForwardGerm_analyticOnNhd F hc hs0 u hu
    rw [regularForwardGerm_eq_actual s hs0 F] at hg
    change AnalyticAt ℂ (fun v => 1+v*exteriorForwardGerm G v) u
    exact analyticAt_const.add (analyticAt_id.mul hg)
  have hh : AnalyticOnNhd ℂ (fun u => (exteriorPhi G u)^n)
      (Metric.ball (0 : ℂ) s⁻¹) := fun u hu => (hPhi u hu).pow n
  have hR : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0,hs1⟩
  have hcoeff := analytic_actualTaylorCoeff_norm_le_circleAverage _ hR hh (n+1)
  rw [← exteriorFormalResidue_eq_actualLaurentCoeff G hG n,
    ← exteriorInverseCoeff_mul_eq_formalResidue G hG n hn] at hcoeff
  have hnNorm : ‖(n : ℂ)‖=(n : ℝ) := by simp
  rw [norm_mul,hnNorm] at hcoeff
  have havg : Real.circleAverage (fun ζ => ‖(exteriorPhi G ζ)^n‖) 0 1 =
      Real.circleAverage (fun ζ => ‖G ζ‖^n) 0 1 := by
    calc
      _ = Real.circleAverage (fun ζ => ‖G ζ⁻¹‖^n) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro ζ hζ
        change ‖(exteriorPhi G ζ)^n‖=‖G ζ⁻¹‖^n
        have hζn : ‖ζ‖=1 := by
          simpa only [abs_one,Metric.mem_sphere,dist_zero_right] using hζ
        have hζ0 : ζ ≠ 0 := by intro h; simp [h] at hζn
        have hp : exteriorPhi G ζ=ζ*G ζ⁻¹ := by
          rw [exteriorPhi,exteriorForwardGerm_punctured G hζ0]
          field_simp [hζ0]
          <;> ring
        rw [norm_pow,hp,norm_mul,hζn,one_mul]
      _ = _ := Real.circleAverage_zero_one_congr_inv (f := fun ζ : ℂ => ‖G ζ‖^n)
  rw [havg] at hcoeff
  exact hcoeff

/-- The genuine candidate condition on the original F yields a lower
moment budget for every regularization, with the correct s^(n+1) factor. -/
theorem rescaleExterior_boundary_moment_ge_of_inverseCoeff_candidate
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (n : ℕ) (hn : 1 ≤ n) (C : ℝ)
    (hC : C ≤ ‖exteriorInverseCoeff F n‖) :
    s^(n+1)*(n : ℝ)*C ≤
      Real.circleAverage (fun ζ => ‖rescaleExterior s F ζ‖^n) 0 1 := by
  have h := rescaleExterior_inverseCoeff_mul_norm_le_boundary_moment F hc hs0 hs1 n hn
  rw [rescaleExterior_inverseCoeff F hc hs0 hs1 hn,norm_mul,norm_pow] at h
  have hsn : ‖(s : ℂ)‖=s := by simp [abs_of_pos hs0]
  rw [hsn] at h
  calc
    _ ≤ s^(n+1)*(n : ℝ)*‖exteriorInverseCoeff F n‖ :=
      mul_le_mul_of_nonneg_left hC (mul_nonneg (pow_nonneg hs0.le _) (Nat.cast_nonneg n))
    _ = (n : ℝ)*(s^(n+1)*‖exteriorInverseCoeff F n‖) := by ring
    _ ≤ _ := h

end SpringerLean
