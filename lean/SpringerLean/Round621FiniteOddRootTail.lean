import SpringerLean.Round69WeightedArea
import SpringerLean.Round620StripLogKernel

namespace SpringerLean
set_option Elab.async false

/-- Finite Cauchy--Schwarz estimate for the actual odd modes, with the
first area mode removed and the exact logarithmic kernel. No oddness is
needed for this finite estimate; it is applied to the odd root later. -/
theorem exteriorForwardCoeff_finite_odd_tail_sq_le
    (H : ℂ → ℂ) (hc : CenteredExteriorUnivalent H)
    {r : ℝ} (hr : 1 < r) {z : ℂ} (hz : ‖z‖ = r) (M : ℕ) :
    ‖∑ k ∈ Finset.range M,
        (z⁻¹)^(2*k+3) * exteriorForwardCoeff H (2*k+3)‖ ^ 2 ≤
      (1-‖exteriorForwardCoeff H 1‖^2) * exteriorStripLogKernel r := by
  classical
  let S := (Finset.range M).image (fun k : ℕ => 2*k+3)
  have hinj : Function.Injective (fun k : ℕ => 2*k+3) := by
    intro a b h
    dsimp only at h
    omega
  have hsub : S ⊆ Finset.Icc 2 (2*M+3) := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    have hkM := Finset.mem_range.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have harea := exteriorForwardCoeff_finite_area_tail H hc (2*M+3) (by omega)
  have hB : (∑ k ∈ Finset.range M,
        ((2*k+3 : ℕ) : ℝ)*‖exteriorForwardCoeff H (2*k+3)‖^2) ≤
      1-‖exteriorForwardCoeff H 1‖^2 := by
    calc
      _ = ∑ j ∈ S, (j : ℝ)*‖exteriorForwardCoeff H j‖^2 := by
        simp only [S,Finset.sum_image hinj.injOn]
      _ ≤ ∑ j ∈ Finset.Icc 2 (2*M+3),
          (j : ℝ)*‖exteriorForwardCoeff H j‖^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by
          intro j hj hjnot
          positivity)
      _ ≤ _ := harea
  have hE : 0 ≤ 1-‖exteriorForwardCoeff H 1‖^2 := by
    have h := exteriorForwardCoeff_finite_area H hc 1
    norm_num at h
    nlinarith [norm_nonneg (exteriorForwardCoeff H 1)]
  have hw : ∀ k ∈ Finset.range M, (0 : ℝ) < ((2*k+3 : ℕ) : ℝ) := by
    intro k hk
    positivity
  have hcs := finiteComplexWeightedSum_sq_le (Finset.range M)
    (fun k : ℕ => ((2*k+3 : ℕ) : ℝ)) hw
    (fun k => (z⁻¹)^(2*k+3)) (fun k => exteriorForwardCoeff H (2*k+3))
  have hA : (∑ k ∈ Finset.range M,
      ‖(z⁻¹)^(2*k+3)‖^2/((2*k+3 : ℕ) : ℝ)) ≤ exteriorStripLogKernel r := by
    have hk := sum_le_hasSum (Finset.range M)
      (fun k _ => by positivity)
      (exteriorStripLogKernel_hasSum hr)
    convert hk using 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [norm_pow,norm_inv,hz,← pow_mul,Nat.mul_comm (2*k+3) 2]
    norm_cast
  have hA0 : 0 ≤ ∑ k ∈ Finset.range M,
      ‖(z⁻¹)^(2*k+3)‖^2/((2*k+3 : ℕ) : ℝ) := by positivity
  calc
    _ ≤ _ := hcs
    _ ≤ (∑ k ∈ Finset.range M,
        ‖(z⁻¹)^(2*k+3)‖^2/((2*k+3 : ℕ) : ℝ)) *
        (1-‖exteriorForwardCoeff H 1‖^2) := mul_le_mul_of_nonneg_left hB hA0
    _ ≤ exteriorStripLogKernel r*(1-‖exteriorForwardCoeff H 1‖^2) :=
      mul_le_mul_of_nonneg_right hA hE
    _ = _ := mul_comm _ _

end SpringerLean
