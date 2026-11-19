import SpringerLean.Round2059LemniscateLocalLog
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Order.Compact

open Set Metric Filter
open scoped Topology

namespace SpringerLean

theorem reciprocalSeparation_isOpen
    (K : Set ℂ) (hK : IsCompact K) (ε : ℝ) :
    IsOpen (reciprocalSeparation K ε) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let B : Set (ℂ × K) := {p | ‖1 - (p.2 : ℂ)*p.1‖ ≤ ε * ‖p.1‖}
  have hB : IsClosed B := isClosed_le (by fun_prop) (by fun_prop)
  have heq : (reciprocalSeparation K ε)ᶜ = Prod.fst '' B := by
    ext u
    constructor
    · intro hu
      have h : ¬∀ a ∈ K, ε * ‖u‖ < ‖1 - a*u‖ := hu
      push Not at h
      obtain ⟨a, ha, hbad⟩ := h
      exact ⟨(u, ⟨a, ha⟩), hbad, rfl⟩
    · rintro ⟨⟨u,a⟩, hbad, rfl⟩ hu
      exact (not_lt_of_ge hbad) (hu a a.property)
  exact isClosed_compl_iff.mp (heq.symm ▸ (isClosedMap_fst_of_compactSpace B hB))

theorem reciprocalSeparation_antitone (K : Set ℂ) :
    Antitone (reciprocalSeparation K) := by
  intro δ ε h u hu a ha
  exact (mul_le_mul_of_nonneg_right h (norm_nonneg u)).trans_lt (hu a ha)

/-- A compact path in the reciprocal domain is separated uniformly
from every reciprocal pole from the compact omitted set. -/
theorem reciprocalSeparation_path_uniform
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    {u : ℂ} (γ : Path 0 u)
    (hγ : ∀ t, γ t ∈ reciprocalSeparation K 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, γ t ∈ reciprocalSeparation K ε := by
  let E : Set ℂ := range γ
  have hE : IsCompact E := isCompact_range γ.continuous
  have hNE : E.Nonempty := range_nonempty _
  let f : ℂ × ℂ → ℝ := fun p => ‖1 - p.1 * p.2‖
  have hf : Continuous f := by fun_prop
  obtain ⟨q, hq, hmin⟩ := (hK.prod hE).exists_isMinOn
    (hne.prod hNE) hf.continuousOn
  have hmin0 : 0 < f q := by
    obtain ⟨t, ht⟩ := hq.2
    have h := hγ t q.1 hq.1
    rw [ht, zero_mul] at h
    exact h
  obtain ⟨B, hB⟩ := (hE.image continuous_norm).bddAbove
  let M := max 0 B + 1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨f q / (2*M), div_pos hmin0 (by positivity), ?_⟩
  intro t a ha
  have hbound : ‖γ t‖ ≤ M := by
    have hb : ‖γ t‖ ≤ B := hB ⟨γ t, mem_range_self t, rfl⟩
    dsimp [M]
    linarith [le_max_right (0 : ℝ) B]
  have hmul := mul_le_mul_of_nonneg_left hbound (div_nonneg hmin0.le (by positivity : 0 ≤ 2*M))
  have hcancel : f q / (2*M) * M = f q / 2 := by
    field_simp [hM.ne']
  rw [hcancel] at hmul
  have hlt : f q / 2 < f q := by linarith
  exact (hmul.trans_lt hlt).trans_le
    (show f q ≤ f (a, γ t) from hmin (show (a, γ t) ∈ K ×ˢ E from ⟨ha, mem_range_self t⟩))

private theorem normalized_analytic_logs_eqOn
    (U : Set ℂ) (hU : IsOpen U) (hconn : IsPreconnected U) (hzero : (0 : ℂ) ∈ U)
    (L M : ℂ → ℂ) (hL : AnalyticOnNhd ℂ L U) (hM : AnalyticOnNhd ℂ M U)
    (hL0 : L 0 = 0) (hM0 : M 0 = 0)
    (hexp : ∀ u ∈ U, Complex.exp (L u) = Complex.exp (M u)) :
    EqOn L M U := by
  apply hL.eqOn_of_preconnected_of_eventuallyEq hM hconn hzero
  have hLnear : ∀ᶠ u in 𝓝 (0 : ℂ), (L u).im ∈ Ioo (-Real.pi) Real.pi := by
    apply (Complex.continuous_im.continuousAt.comp (hL 0 hzero).continuousAt).eventually
    rw [Function.comp_apply, hL0, Complex.zero_im]
    exact isOpen_Ioo.mem_nhds ⟨by linarith [Real.pi_pos], Real.pi_pos⟩
  have hMnear : ∀ᶠ u in 𝓝 (0 : ℂ), (M u).im ∈ Ioo (-Real.pi) Real.pi := by
    apply (Complex.continuous_im.continuousAt.comp (hM 0 hzero).continuousAt).eventually
    rw [Function.comp_apply, hM0, Complex.zero_im]
    exact isOpen_Ioo.mem_nhds ⟨by linarith [Real.pi_pos], Real.pi_pos⟩
  filter_upwards [hLnear, hMnear, hU.mem_nhds hzero] with u hLu hMu hu
  have h := congrArg Complex.log (hexp u hu)
  rwa [Complex.log_exp hLu.1 hLu.2.le, Complex.log_exp hMu.1 hMu.2.le] at h

/-- The normalized local logs glue over the reciprocal domain when
that domain is connected. Each point can be joined to reciprocal
infinity on a compact path, so it belongs to one separated component. -/
theorem reciprocal_ratio_global_analytic_log
    (K : Set ℂ) (hK : IsCompact K) (hconn : IsConnected K)
    (hU : IsConnected (reciprocalSeparation K 0))
    (a b : ℂ) (ha : a ∈ K) (hb : b ∈ K) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L (reciprocalSeparation K 0) ∧ L 0 = 0 ∧
      ∀ u ∈ reciprocalSeparation K 0,
        Complex.exp (L u) = (1-a*u)/(1-b*u) := by
  classical
  let W (ε : ℝ) := connectedComponentIn (reciprocalSeparation K ε) (0 : ℂ)
  have hWO (ε : ℝ) : IsOpen (W ε) := (reciprocalSeparation_isOpen K hK ε).connectedComponentIn
  have hW0 (ε : ℝ) : (0 : ℂ) ∈ W ε :=
    mem_connectedComponentIn (zero_mem_reciprocalSeparation K ε)
  have hWsub (ε : ℝ) : W ε ⊆ reciprocalSeparation K ε := connectedComponentIn_subset _ _
  have hWanti : Antitone W := fun _ _ h =>
    connectedComponentIn_mono _ (reciprocalSeparation_antitone K h)
  have hcover (u : ℂ) (hu : u ∈ reciprocalSeparation K 0) :
      ∃ ε : {ε : ℝ // 0 < ε}, u ∈ W ε := by
    have hpath := IsPathConnected.joinedIn
      ((reciprocalSeparation_isOpen K hK 0).isConnected_iff_isPathConnected.mp hU)
      0 (zero_mem_reciprocalSeparation K 0) u hu
    obtain ⟨γ, hγ⟩ := hpath
    obtain ⟨ε, hε, hsub⟩ := reciprocalSeparation_path_uniform K hK hconn.nonempty γ hγ
    have hγconn := isConnected_range γ.continuous
    have hγsub : range γ ⊆ reciprocalSeparation K ε := by
      rintro _ ⟨t,rfl⟩
      exact hsub t
    have hγ0 : (0 : ℂ) ∈ range γ := ⟨0, γ.source⟩
    have hγ1 : u ∈ range γ := ⟨1, γ.target⟩
    exact ⟨⟨ε,hε⟩, hγconn.isPreconnected.subset_connectedComponentIn hγ0 hγsub hγ1⟩
  choose L hLa hL0 hLexp using fun ε : {ε : ℝ // 0 < ε} =>
    reciprocal_ratio_analytic_log_on_separation K hconn.isPreconnected ε ε.2 a b ha hb
  let G (u : ℂ) := if hu : u ∈ reciprocalSeparation K 0 then L (hcover u hu).choose u else 0
  have hlocal (ε : {ε : ℝ // 0 < ε}) : EqOn (L ε) G (W ε) := by
    intro u hu
    have hu0 := reciprocalSeparation_antitone K ε.2.le (hWsub ε hu)
    simp only [G, dite_eq_left hu0]
    let δ := (hcover u hu0).choose
    have hδ : u ∈ W δ := (hcover u hu0).choose_spec
    let η := max (ε : ℝ) (δ : ℝ)
    have hcompL : W η ⊆ reciprocalSeparation K ε :=
      (hWanti (le_max_left _ _)).trans (hWsub ε)
    have hcompM : W η ⊆ reciprocalSeparation K δ :=
      (hWanti (le_max_right _ _)).trans (hWsub δ)
    have hη : u ∈ W η := by
      rcases le_total (ε : ℝ) δ with h | h
      · simpa [η, max_eq_right h] using hδ
      · simpa [η, max_eq_left h] using hu
    exact normalized_analytic_logs_eqOn (W η) (hWO η) isPreconnected_connectedComponentIn
      (hW0 η) (L ε) (L δ) ((hLa ε).mono hcompL) ((hLa δ).mono hcompM)
      (hL0 ε) (hL0 δ) (fun v hv => (hLexp ε v (hcompL hv)).trans
        (hLexp δ v (hcompM hv)).symm) hη
  refine ⟨G, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨ε,hεu⟩ := hcover u hu
    exact (AnalyticOnNhd.congr (hWO ε) ((hLa ε).mono (hWsub ε)) (hlocal ε)) u hεu
  · simp [G, zero_mem_reciprocalSeparation, hL0]
  · intro u hu
    obtain ⟨ε,hεu⟩ := hcover u hu
    rw [← hlocal ε hεu]
    exact hLexp ε u (hWsub ε hεu)

end SpringerLean
