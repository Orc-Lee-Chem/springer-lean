import SpringerLean.Round717ActualAngularLocalSubmean
import SpringerLean.Round32VerticalMoments

open MeasureTheory Set Metric

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A weak maximum principle from LOCAL circle submeans only.  This
general compact-set statement does not assume a pre-existing subharmonic
API.  A positive imaginary-coordinate square makes the submean strict. -/
theorem le_of_local_circle_submean_of_compact
    (u : ℂ → ℝ) (K : Set ℂ) (hK : IsCompact K) (hu : ContinuousOn u K)
    (hsub : ∀ z ∈ interior K, ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → u z ≤ Real.circleAverage u z ρ)
    (M : ℝ) (hboundary : ∀ z ∈ frontier K, u z ≤ M) :
    ∀ z ∈ K, u z ≤ M := by
  intro z₀ hz₀
  by_contra hn
  have hgap : 0 < u z₀-M := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  have hR0 : 0 ≤ R := (norm_nonneg z₀).trans (hR z₀ hz₀)
  let κ : ℝ := (u z₀-M)/(2*(R^2+1))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκeq : κ*(2*(R^2+1)) = u z₀-M := by
    dsimp [κ]
    exact div_mul_cancel₀ _ (by positivity)
  have hκbound : κ*R^2 < u z₀-M := by nlinarith [sq_nonneg R]
  let V : ℂ → ℝ := fun z => u z+κ*z.im^2
  have hV : ContinuousOn V K := hu.add (by fun_prop : Continuous (fun z : ℂ => κ*z.im^2)).continuousOn
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨z₀, hz₀⟩ hV
  have hbase : u z₀ ≤ V z := by
    exact (le_add_of_nonneg_right (mul_nonneg hκ.le (sq_nonneg z₀.im))).trans
      (hmax hz₀)
  have hzInterior : z ∈ interior K := by
    by_contra hzNot
    have hzFront : z ∈ frontier K := by
      rw [frontier, hK.isClosed.closure_eq]
      exact ⟨hz, hzNot⟩
    have hzi : z.im^2 ≤ R^2 := by
      have him := Complex.abs_im_le_norm z
      have hnR := hR z hz
      have habs := abs_le.mp (him.trans hnR)
      nlinarith
    have hzB := hboundary z hzFront
    have hVm : V z ≤ M+κ*R^2 := by
      dsimp [V]
      exact add_le_add hzB (mul_le_mul_of_nonneg_left hzi hκ.le)
    linarith
  obtain ⟨r₀, hr₀, hlocal⟩ := hsub z hzInterior
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzInterior)
  let ρ : ℝ := min r₀ d/2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ < r₀ := by dsimp [ρ]; linarith [min_le_left r₀ d]
  have hρd : ρ < d := by dsimp [ρ]; linarith [min_le_right r₀ d]
  have hsphere : sphere z |ρ| ⊆ K := by
    intro w hw
    apply hball
    rw [mem_ball]
    have heq : dist w z = ρ := by simpa only [mem_sphere, abs_of_pos hρ] using hw
    rw [heq]
    exact hρd
  have huci : CircleIntegrable u z ρ := (hu.mono hsphere).circleIntegrable'
  have hqci : CircleIntegrable (fun w : ℂ => κ*w.im^2) z ρ :=
    (by fun_prop : Continuous (fun w : ℂ => κ*w.im^2)).continuousOn.circleIntegrable hρ.le
  have hVci : CircleIntegrable V z ρ := huci.add hqci
  have hqmean : Real.circleAverage (fun w : ℂ => κ*w.im^2) z ρ =
      κ*(z.im^2+ρ^2/2) := by
    have heq : (fun w : ℂ => κ*w.im^2) = κ • (fun w : ℂ => w.im^2) := rfl
    rw [heq, Real.circleAverage_smul, circleAverage_im_sq]
    rfl
  have hVmean : Real.circleAverage V z ρ =
      Real.circleAverage u z ρ+κ*(z.im^2+ρ^2/2) := by
    rw [show V = (fun w : ℂ => u w+κ*w.im^2) from rfl,
      Real.circleAverage_fun_add huci hqci, hqmean]
  have hstrict : V z < Real.circleAverage V z ρ := by
    rw [hVmean]
    have hl := hlocal ρ hρ hρr
    have hp : 0 < κ*(ρ^2/2) := by positivity
    dsimp [V]
    nlinarith
  have hupper : Real.circleAverage V z ρ ≤ V z :=
    Real.circleAverage_mono_on_of_le_circle hVci (fun w hw => hmax (hsphere hw))
  exact (not_lt_of_ge hupper) hstrict

end SpringerLean

#print axioms SpringerLean.le_of_local_circle_submean_of_compact
