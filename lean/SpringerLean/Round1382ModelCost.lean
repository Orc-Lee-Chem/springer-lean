import SpringerLean.Round1381ActiveCost

open MeasureTheory

namespace SpringerLean

theorem coarseInverseModelCircle_le_sharp (n : ℕ) :
    Real.circleAverage
      (fun ζ : ℂ => coarseInverseRadius (2*ζ.re)^n) 0 1 ≤
    (39/20 : ℝ)^n +
      (Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1 / 2) *
        (1+800/(79*(((n+2:ℕ):ℝ)))) := by
  let f : ℝ → ℝ := fun θ => coarseInverseRadius (2*Real.cos θ)^n
  have hfcont : Continuous f := by
    dsimp [f]
    have hcos : Continuous (fun θ : ℝ => 2*Real.cos θ) := by fun_prop
    exact (coarseInverseRadius_continuous.comp hcos).pow n
  have hα0 : 0 ≤ coarseAngleAlpha := Real.arccos_nonneg _
  have hαπ : coarseAngleAlpha ≤ Real.pi := Real.arccos_le_pi _
  have hfull := evenCos_circleAverage_eq_integral
    (fun x : ℝ => coarseInverseRadius x^n)
    (coarseInverseRadius_continuous.pow n)
  have hsplit :
      (∫ θ in (0:ℝ)..Real.pi, f θ) =
      (∫ θ in (0:ℝ)..coarseAngleAlpha, f θ) +
      (∫ θ in coarseAngleAlpha..Real.pi, f θ) := by
    have h₁ : IntervalIntegrable f volume 0 coarseAngleAlpha :=
      hfcont.intervalIntegrable _ _
    have h₂ : IntervalIntegrable f volume coarseAngleAlpha Real.pi :=
      hfcont.intervalIntegrable _ _
    exact (intervalIntegral.integral_add_adjacent_intervals h₁ h₂).symm
  have hplate :
      (∫ θ in coarseAngleAlpha..Real.pi, f θ) =
      (Real.pi-coarseAngleAlpha)*(39/20 : ℝ)^n := by
    have hcongr : (∫ θ in coarseAngleAlpha..Real.pi, f θ) =
        ∫ θ in coarseAngleAlpha..Real.pi, (39/20 : ℝ)^n := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθ' : θ ∈ Set.Icc coarseAngleAlpha Real.pi := by
        simpa [Set.uIcc_of_le hαπ] using hθ
      have hcos : Real.cos θ ≤ 31/32 := by
        have hc := Real.cos_le_cos_of_nonneg_of_le_pi hα0 hθ'.2 hθ'.1
        change Real.cos θ ≤ Real.cos (Real.arccos (31/32 : ℝ)) at hc
        rwa [Real.cos_arccos (by norm_num) (by norm_num)] at hc
      dsimp [f]
      rw [coarseInverseRadius_eq_platform_of_le_threshold (by linarith)]
    rw [hcongr]
    simp
  have hactive := coarseAngle_active_cost_le n
  have hπ : 0 < Real.pi := Real.pi_pos
  have hI := comparisonCircleMoment_eq_halfCosMoment n
  have hactive' :
      (1/Real.pi)*(∫ θ in (0:ℝ)..coarseAngleAlpha, f θ) ≤
      (Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1 / 2) *
        (1+800/(79*(((n+2:ℕ):ℝ)))) := by
    have hh := mul_le_mul_of_nonneg_left hactive
      (show 0 ≤ 1/Real.pi by positivity)
    change (1/Real.pi)*(∫ θ in (0:ℝ)..coarseAngleAlpha, f θ) ≤ _ at hh
    rw [hI]
    convert hh using 1 <;> ring
  have hplatform :
      (1/Real.pi)*((Real.pi-coarseAngleAlpha)*(39/20 : ℝ)^n) ≤
      (39/20 : ℝ)^n := by
    have hfac : 0 ≤ (39/20 : ℝ)^n := by positivity
    have hfrac : 0 ≤ coarseAngleAlpha/Real.pi := div_nonneg hα0 hπ.le
    have hfrac' : coarseAngleAlpha/Real.pi ≤ 1 := (div_le_one hπ).2 hαπ
    have hratio : (Real.pi-coarseAngleAlpha)/Real.pi ≤ 1 := by
      apply (div_le_one hπ).2
      linarith
    calc
      (1/Real.pi)*((Real.pi-coarseAngleAlpha)*(39/20 : ℝ)^n) =
          ((Real.pi-coarseAngleAlpha)/Real.pi)*(39/20 : ℝ)^n := by ring
      _ ≤ 1*(39/20 : ℝ)^n := mul_le_mul_of_nonneg_right hratio hfac
      _ = _ := by ring
  rw [hfull]
  change (1/Real.pi)*(∫ θ in (0:ℝ)..Real.pi, f θ) ≤ _
  rw [hsplit,hplate, mul_add]
  linarith

/-- The strengthened one-end model cost. The `11/n` allowance keeps
the positive-half-circle factor explicit. -/
theorem coarseInverseModelCircle_le_eleven (n : ℕ) (hn : 1 ≤ n) :
    Real.circleAverage
      (fun ζ : ℂ => coarseInverseRadius (2*ζ.re)^n) 0 1 ≤
    (39/20 : ℝ)^n +
      (Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1 / 2) *
        (1+11/(n:ℝ)) := by
  let I : ℝ := Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hn2 : (0:ℝ) < (n+2:ℕ) := by positivity
  have hcoef : (800:ℝ)/(79*(((n+2:ℕ):ℝ))) ≤ 11/(n:ℝ) := by
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<79*(((n+2:ℕ):ℝ))) hn0).2
    push_cast
    nlinarith
  have hC : 0 ≤ halfCosMoment n := by
    unfold halfCosMoment
    exact (EulerSine.integral_cos_pow_pos n).le
  have hI : 0 ≤ I := by
    dsimp [I]
    rw [comparisonCircleMoment_eq_halfCosMoment]
    positivity
  have hmult := mul_le_mul_of_nonneg_left (add_le_add_left hcoef 1)
    (div_nonneg hI (by norm_num : (0:ℝ) ≤ 2))
  have hsharp := coarseInverseModelCircle_le_sharp n
  change _ ≤ (39/20 : ℝ)^n + (I/2)*(1+800/(79*(((n+2:ℕ):ℝ)))) at hsharp
  change _ ≤ (39/20 : ℝ)^n + (I/2)*(1+11/(n:ℝ))
  linarith

theorem coarseInverseModelCircle_le_thirteen (n : ℕ) (hn : 1 ≤ n) :
    Real.circleAverage
      (fun ζ : ℂ => coarseInverseRadius (2*ζ.re)^n) 0 1 ≤
    (39/20 : ℝ)^n +
      (Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1 / 2) *
        (1+13/(n:ℝ)) := by
  have h := coarseInverseModelCircle_le_eleven n hn
  have hI : 0 ≤ Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1 := by
    rw [comparisonCircleMoment_eq_halfCosMoment]
    have hC := (EulerSine.integral_cos_pow_pos n).le
    positivity
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hcoef : 11/(n:ℝ) ≤ 13/(n:ℝ) :=
    div_le_div_of_nonneg_right (by norm_num) hn0.le
  have hh := mul_le_mul_of_nonneg_left (add_le_add_left hcoef 1)
    (div_nonneg hI (by norm_num : (0:ℝ) ≤ 2))
  linarith

end SpringerLean

#print axioms SpringerLean.coarseInverseModelCircle_le_sharp
#print axioms SpringerLean.coarseInverseModelCircle_le_eleven
#print axioms SpringerLean.coarseInverseModelCircle_le_thirteen
