import SpringerLean.Round1482ActualFineWidth

namespace SpringerLean

noncomputable def exteriorFineEndpointWidth (P : ℂ) : ℝ :=
  (exteriorRealRootWidth ‖P‖
    (1+(2/25:ℝ)*Real.sqrt (2-‖P‖)))^2

/-- The boundary localization and earlier exact root-width theorem
put the actual strip in the disk scale needed by the phase proof. -/
theorem exteriorOmitted_actualEndpoint_fine_width_disk_scale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd0 : 0 < 2-‖P‖)
    (hdef : ((2*k-1:ℕ):ℝ)*(2-‖P‖)<3/20)
    (hlog : ((2*k-1:ℕ):ℝ)*(2-‖P‖)*
      Real.log (2/(2-‖P‖))<3/2) :
    exteriorFineEndpointWidth P <
      (1/3:ℝ)*(2-‖P‖)*Real.log (2/(2-‖P‖)) ∧
    ((2*k-2:ℕ):ℝ)*exteriorFineEndpointWidth P < 1/2 := by
  have hconv : P ∈ convexHull ℝ (exteriorOmitted F) :=
    subset_convexHull ℝ (exteriorOmitted F) hP
  have hstrip := exteriorOmitted_actualEndpoint_fine_strip
    F hc k hk P hP hd0 hdef P hconv
  have hW : exteriorFineEndpointWidth P <
      (1/3:ℝ)*(2-‖P‖)*Real.log (2/(2-‖P‖)) := by
    exact hstrip.1
  let n : ℕ := 2*k-1
  let m : ℕ := 2*k-2
  have hmNat : m ≤ n := by dsimp [m,n]; omega
  have hm : ((m:ℝ) ≤ (n:ℝ)) := by exact_mod_cast hmNat
  have hnNat : 1501 ≤ n := by dsimp [n]; omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hW0 : 0 ≤ exteriorFineEndpointWidth P :=
    sq_nonneg _
  have hmn := mul_le_mul_of_nonneg_right hm hW0
  have hnW := mul_lt_mul_of_pos_left hW hn0
  refine ⟨hW,?_⟩
  change (m:ℝ)*exteriorFineEndpointWidth P < 1/2
  change (n:ℝ)*(2-‖P‖)*Real.log (2/(2-‖P‖)) < 3/2 at hlog
  nlinarith [hmn,hnW]

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_actualEndpoint_fine_width_disk_scale
