import SpringerLean.Round692AngularTopHeight
import SpringerLean.Round693AngularTopUniform
import SpringerLean.Round697ActualDiskLipschitz

open MeasureTheory Set Metric

namespace SpringerLean
set_option Elab.async false

/-- Joint quantitative continuity of the SAME actual top functional on
a fixed closed radial subdisk and interior angular masses. All derivative
and optimizer inputs are derived from the original function class. -/
theorem actualAngularTopValue_exists_joint_lipschitz_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (c : ℂ) (r : ℝ), r ∈ Icc 0 R →
      ∀ r' ∈ Icc 0 R, ∀ h ∈ Ioo 0 Real.pi, ∀ h' ∈ Ioo 0 Real.pi,
      |actualAngularTopValue F c r h-actualAngularTopValue F c r' h'| ≤
        (2*Real.pi*‖c‖*L)*|r-r'|+(4*‖c‖*R)*|h-h'| := by
  obtain ⟨L, hL0, hL⟩ :=
    actualHarmonic_angular_projection_exists_radius_lipschitz F hc hR0 hR1
  refine ⟨L, hL0, ?_⟩
  intro c r hr r' hr' h hh h' hh'
  have hr1 : r < 1 := lt_of_le_of_lt hr.2 hR1
  have hr'1 : r' < 1 := lt_of_le_of_lt hr'.2 hR1
  have hrad := actualAngularTopValue_abs_sub_le_uniform F F hc hc c c
    hr.1 hr1 hr'.1 hr'1 hh.1 hh.2 (‖c‖*L*|r-r'|)
    (fun θ _ => hL r hr r' hr' c θ)
  have hrad' : |actualAngularTopValue F c r h-actualAngularTopValue F c r' h| ≤
      (2*Real.pi*‖c‖*L)*|r-r'| := by
    calc
      _ ≤ 2*h*(‖c‖*L*|r-r'|) := hrad
      _ ≤ 2*Real.pi*(‖c‖*L*|r-r'|) :=
        mul_le_mul_of_nonneg_right (by linarith [hh.2] : 2*h ≤ 2*Real.pi) (by positivity)
      _ = (2*Real.pi*‖c‖*L)*|r-r'| := by ring
  have hheight := actualAngularTopValue_height_lipschitz F hc c hr'.1 hr'1
    hh.1 hh.2 hh'.1 hh'.2
  have hheight' : |actualAngularTopValue F c r' h-actualAngularTopValue F c r' h'| ≤
      (4*‖c‖*R)*|h-h'| := by
    calc
      _ ≤ (4*‖c‖*r')*|h-h'| := hheight
      _ ≤ (4*‖c‖*R)*|h-h'| := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hr'.2 (by positivity)) (abs_nonneg _)
  exact (abs_sub_le _ _ _).trans (add_le_add hrad' hheight')

theorem actualAngularTopValue_continuousOn_subrectangle
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    ContinuousOn (fun p : ℝ × ℝ => actualAngularTopValue F c p.1 p.2)
      (Icc 0 R ×ˢ Ioo 0 Real.pi) := by
  obtain ⟨L, hL0, hL⟩ := actualAngularTopValue_exists_joint_lipschitz_bound F hc hR0 hR1
  let A : ℝ := 2*Real.pi*‖c‖*L
  let B : ℝ := 4*‖c‖*R
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let K : NNReal := ⟨A+B, add_nonneg hA hB⟩
  have hLip : LipschitzOnWith K
      (fun p : ℝ × ℝ => actualAngularTopValue F c p.1 p.2)
      (Icc 0 R ×ˢ Ioo 0 Real.pi) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    have hnum := hL c p.1 hp.1 q.1 hq.1 p.2 hp.2 q.2 hq.2
    have hfst : |p.1-q.1| ≤ dist p q := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact le_max_left _ _
    have hsnd : |p.2-q.2| ≤ dist p q := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact le_max_right _ _
    rw [Real.dist_eq]
    calc
      _ ≤ A*|p.1-q.1|+B*|p.2-q.2| := hnum
      _ ≤ A*dist p q+B*dist p q := add_le_add
        (mul_le_mul_of_nonneg_left hfst hA) (mul_le_mul_of_nonneg_left hsnd hB)
      _ = (K : ℝ)*dist p q := by change _ = (A+B)*dist p q; ring
  exact hLip.continuousOn

end SpringerLean
