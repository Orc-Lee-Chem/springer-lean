import SpringerLean.Analytic

namespace SpringerLean

/-- The rescaled exterior domain, which includes the unit circle when `s < 1`. -/
def exteriorAbove (s : ℝ) : Set ℂ := {z | s < ‖z‖}

/-- The manuscript's approximation `F_s(z) = s F(z/s)`. -/
noncomputable def rescaleExterior (s : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (s : ℂ) * F (z / (s : ℂ))

theorem div_mem_exteriorDisk {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z ∈ exteriorAbove s) : z / (s : ℂ) ∈ exteriorDisk := by
  have hsn : ‖(s : ℂ)‖ = s := by simp [abs_of_pos hs]
  change 1 < ‖z / (s : ℂ)‖
  rw [norm_div, hsn]
  exact (one_lt_div hs).mpr hz

theorem rescaleExterior_injOn {s : ℝ} (hs : 0 < s) {F : ℂ → ℂ}
    (hF : Set.InjOn F exteriorDisk) :
    Set.InjOn (rescaleExterior s F) (exteriorAbove s) := by
  intro z hz w hw h
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  have h' : F (z / (s : ℂ)) = F (w / (s : ℂ)) := by
    exact (mul_left_cancel₀ hs0 h)
  have hzw := hF (div_mem_exteriorDisk hs hz) (div_mem_exteriorDisk hs hw) h'
  have := congrArg (fun x : ℂ => x * (s : ℂ)) hzw
  field_simp [hs0] at this
  exact this


/-- Holomorphy is retained on the enlarged domain under the same rescaling. -/
theorem rescaleExterior_analyticAt {s : ℝ} (hs : 0 < s) {F : ℂ → ℂ}
    (hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z) {z : ℂ}
    (hz : z ∈ exteriorAbove s) : AnalyticAt ℂ (rescaleExterior s F) z := by
  let T : ℂ → ℂ := fun y => y / (s : ℂ)
  have hdiv : AnalyticAt ℂ T z := by
    dsimp [T]
    exact analyticAt_id.div_const
  have hcomp : AnalyticAt ℂ (F ∘ T) z :=
    (hF (T z) (div_mem_exteriorDisk hs hz)).comp hdiv
  have hmul : AnalyticAt ℂ ((fun _ : ℂ => (s : ℂ)) * (F ∘ T)) z :=
    analyticAt_const.mul hcomp
  have heq : ((fun _ : ℂ => (s : ℂ)) * (F ∘ T)) = rescaleExterior s F := by
    funext y
    rfl
  rw [heq] at hmul
  exact hmul

/-- For `s < 1`, the circle `|z|=1` lies strictly inside the rescaled analytic domain. -/
theorem unitCircle_subset_exteriorAbove {s : ℝ} (hs : s < 1) :
    {z : ℂ | ‖z‖ = 1} ⊆ exteriorAbove s := by
  intro z hz
  change s < ‖z‖
  rw [hz]
  exact hs
end SpringerLean