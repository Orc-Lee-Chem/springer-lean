import SpringerLean.Round1873PolynomialLemniscateBridge
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Connected.LocallyConnected

open Set Metric Polynomial

namespace SpringerLean

theorem complex_norm_gt_isConnected (R : ℝ) (hR : 0 ≤ R) :
    IsConnected {z : ℂ | R < ‖z‖} := by
  have hdim : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  let f : ℝ × ℂ → ℂ := fun p => p.1 • p.2
  have hcont : Continuous f := continuous_fst.smul continuous_snd
  have himage : f '' (Ioi R ×ˢ sphere (0 : ℂ) 1) = {z : ℂ | R < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨r,w⟩, ⟨hr, hw⟩, rfl⟩
      have hr0 : 0 ≤ r := hR.trans (le_of_lt hr)
      have hw' : ‖w‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hw
      change R < ‖r • w‖
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0, hw', mul_one, mem_Ioi] using hr
    · intro hz
      change R < ‖z‖ at hz
      have hz0 : 0 < ‖z‖ := hR.trans_lt hz
      refine ⟨(‖z‖, (‖z‖⁻¹ : ℝ) • z), ⟨hz, ?_⟩, ?_⟩
      · simp [hz0.ne']
      · simp [f, hz0.ne']
  rw [← himage]
  exact (isConnected_Ioi.prod (isConnected_sphere hdim 0 (by norm_num))).image _
    hcont.continuousOn

theorem polynomial_unit_lemniscate_isCompact (Q : ℂ[X]) (hQ : 0 < Q.natDegree) :
    IsCompact {z : ℂ | ‖Q.eval z‖ ≤ 1} := by
  have hp : 0 < Q.degree := (natDegree_pos_iff_degree_pos).mp hQ
  convert (Q.isProperMap_eval hp).isCompact_preimage (isCompact_closedBall (0 : ℂ) 1) using 1
  ext z
  simp [mem_closedBall, dist_zero_right]

/-- The complement of a polynomial unit sublevel set is connected.
Polynomial openness and properness make each component map onto the
whole exterior value disk. Each therefore meets the connected region
beyond a common bounding disk. -/
theorem polynomial_unit_lemniscate_exterior_isConnected
    (Q : ℂ[X]) (hQ : 0 < Q.natDegree) :
    IsConnected {z : ℂ | 1 < ‖Q.eval z‖} := by
  let D : Set ℂ := {z | 1 < ‖z‖}
  let Ω : Set ℂ := Q.eval ⁻¹' D
  have hD : IsConnected D := complex_norm_gt_isConnected 1 (by norm_num)
  have hopen : IsOpen Ω := isOpen_lt continuous_const Q.continuous.norm
  have : LocallyConnectedSpace Ω := hopen.locallyConnectedSpace
  let q : Ω → D := fun z => ⟨Q.eval z, z.2⟩
  have hopenq : IsOpenMap q := (complexPolynomial_isOpenMap_eval Q hQ).restrictPreimage D
  have hclosedq : IsClosedMap q := Q.isClosedMap_eval.restrictPreimage D
  have : PreconnectedSpace D := Subtype.preconnectedSpace hD.isPreconnected
  have hK := polynomial_unit_lemniscate_isCompact Q hQ
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).mp hK.isBounded
  let r := max R 1
  have hr : 0 ≤ r := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_right _ _)
  let S : Set ℂ := {z | r < ‖z‖}
  have hS : IsConnected S := complex_norm_gt_isConnected r hr
  have hSΩ : S ⊆ Ω := by
    intro z hz
    change 1 < ‖Q.eval z‖
    by_contra! h
    have hnorm : ‖z‖ ≤ R := by
      simpa only [mem_closedBall, dist_zero_right] using hR h
    exact (not_lt_of_ge (hnorm.trans (le_max_left _ _))) hz
  have hcomponent (x : Ω) : q '' connectedComponent x = univ := by
    have hcl : IsClopen (connectedComponent x) :=
      ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩
    have hi : IsClopen (q '' connectedComponent x) :=
      ⟨hclosedq _ hcl.1, hopenq _ hcl.2⟩
    rcases isClopen_iff.mp hi with he | h
    · have hmem : q x ∈ q '' connectedComponent x := ⟨x, mem_connectedComponent, rfl⟩
      simp [he] at hmem
    · exact h
  have hmeet (x : Ω) : ∃ y ∈ connectedComponent x, (y : ℂ) ∈ S := by
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) r).image Q.continuous.norm |>.bddAbove
    let y : D := ⟨((|B|+2 : ℝ) : ℂ), by
      change 1 < ‖((|B|+2 : ℝ) : ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith [abs_nonneg B]⟩
    have hy : y ∈ q '' connectedComponent x := by rw [hcomponent]; trivial
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨z, hz, ?_⟩
    change r < ‖(z : ℂ)‖
    by_contra! hx
    have hzball : (z : ℂ) ∈ closedBall (0 : ℂ) r := by
      simpa only [mem_closedBall, dist_zero_right] using hx
    have hle : ‖Q.eval (z : ℂ)‖ ≤ B := hB ⟨(z : ℂ), hzball, rfl⟩
    have heq : Q.eval (z : ℂ) = ((|B|+2 : ℝ) : ℂ) := congrArg Subtype.val hzy
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hle
    linarith [le_abs_self B]
  let liftS : S → Ω := fun z => ⟨z, hSΩ z.property⟩
  have hSrange : IsConnected (range liftS) := by
    have : ConnectedSpace S := isConnected_iff_connectedSpace.mp hS
    exact isConnected_range (continuous_subtype_val.subtype_mk _)
  obtain ⟨x₀, hx₀⟩ := hSrange.nonempty
  have hSuniv : connectedComponent x₀ = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨y, hy, hyS⟩ := hmeet x
    have hy' : y ∈ range liftS := ⟨⟨y, hyS⟩, Subtype.ext rfl⟩
    have hy₀ := hSrange.isPreconnected.subset_connectedComponent hx₀ hy'
    rw [connectedComponent_eq hy₀, ← connectedComponent_eq hy]
    exact mem_connectedComponent
  have hΩ : IsConnected (univ : Set Ω) := hSuniv ▸ isConnected_connectedComponent
  change IsConnected Ω
  have h := hΩ.image (Subtype.val : Ω → ℂ) continuous_subtype_val.continuousOn
  simpa using h

end SpringerLean
