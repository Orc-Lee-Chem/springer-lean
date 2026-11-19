import SpringerLean.Round11Energy
import SpringerLean.Round09OmittedLimit
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.MetricSpace.Bounded

open Filter
open scoped Topology

namespace SpringerLean

/-- A holomorphic exterior injection has open image on every open subset of
its actual source domain. This is the local open mapping theorem; the
locally constant alternative is excluded by injectivity. -/
theorem exterior_image_open_of_isOpen
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ exteriorDisk) :
    IsOpen (F '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro w ⟨z, hzU, rfl⟩
  have hAnalytic : AnalyticAt ℂ F z :=
    hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds (hsub hzU))
  have hNotConst : ¬∀ᶠ u in 𝓝 z, F u = F z := by
    intro hevent
    have hboth : {u : ℂ | u ∈ U ∧ F u = F z} ∈ 𝓝 z := by
      filter_upwards [hU.mem_nhds hzU, hevent] with u hu hFu
      exact ⟨hu, hFu⟩
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hboth
    let u : ℂ := z + (δ / 2 : ℝ)
    have huBall : u ∈ Metric.ball z δ := by
      change dist u z < δ
      rw [dist_eq_norm]
      have heq : u - z = ((δ / 2 : ℝ) : ℂ) := by
        dsimp [u]
        ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hδ)]
      linarith
    obtain ⟨huU, huF⟩ := hball huBall
    have hEq : u = z := hc.2.1 (hsub huU) (hsub hzU) huF
    have hNe : u ≠ z := by
      intro heq
      have hzero : ((δ / 2 : ℝ) : ℂ) = 0 := by
        dsimp [u] at heq
        exact add_left_cancel (show z + ((δ / 2 : ℝ) : ℂ) = z + 0 by
          simpa using heq)
      exact (ne_of_gt (half_pos hδ)) (by exact_mod_cast hzero)
    exact hNe hEq
  have hMap :=
    hAnalytic.eventually_constant_or_nhds_le_map_nhds.resolve_left hNotConst
  have hImage : F '' U ∈ map F (𝓝 z) :=
    Filter.image_mem_map (hU.mem_nhds hzU)
  exact hMap hImage

/-- The genuine omitted set is compact, with no boundary extension added
to the exterior class. -/
theorem exteriorOmitted_isCompact
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    IsCompact (exteriorOmitted F) := by
  have hOpen : IsOpen (F '' exteriorDisk) :=
    exterior_image_open_of_isOpen F hc exteriorDisk_isOpen subset_rfl
  have hClosed : IsClosed (exteriorOmitted F) := by
    simpa only [exteriorOmitted] using hOpen.isClosed_compl
  obtain ⟨M, hM0, hM⟩ := exteriorOmitted_bounded F hc
  have hBdd : Bornology.IsBounded (exteriorOmitted F) := by
    exact isBounded_iff_forall_norm_le.mpr ⟨M, hM⟩
  exact (Metric.isCompact_iff_isClosed_bounded).mpr ⟨hClosed, hBdd⟩

/-- Each unscaled intermediate omitted set is compact. -/
theorem exteriorOmittedAtScale_isCompact
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    IsCompact (exteriorOmittedAtScale F s) := by
  have hInv : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  have hsub : exteriorAbove s⁻¹ ⊆ exteriorDisk := by
    intro z hz
    exact lt_trans hInv hz
  have hOpen : IsOpen (F '' exteriorAbove s⁻¹) :=
    exterior_image_open_of_isOpen F hc
      (isOpen_lt continuous_const continuous_norm) hsub
  have hClosed : IsClosed (exteriorOmittedAtScale F s) := by
    simpa only [exteriorOmittedAtScale] using hOpen.isClosed_compl
  obtain ⟨M, hM0, hM⟩ := exteriorOmittedAtScale_bounded F hc hs0 hs1
  have hBdd : Bornology.IsBounded (exteriorOmittedAtScale F s) := by
    exact isBounded_iff_forall_norm_le.mpr ⟨M, hM⟩
  exact (Metric.isCompact_iff_isClosed_bounded).mpr ⟨hClosed, hBdd⟩

end SpringerLean
