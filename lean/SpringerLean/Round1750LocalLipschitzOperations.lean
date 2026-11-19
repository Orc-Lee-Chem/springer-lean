import SpringerLean.Round1746ActualTimeLocalLipschitz

open Filter
open scoped Topology

namespace SpringerLean

theorem contDiffAt_complex_mk
    (f g : ℂ → ℝ) (z : ℂ)
    (hf : ContDiffAt ℝ 1 f z) (hg : ContDiffAt ℝ 1 g z) :
    ContDiffAt ℝ 1 (fun w => Complex.mk (f w) (g w)) z := by
  have h := Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp z (hf.prodMk hg)
  convert h using 1
  ext w
  apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply]

theorem local_lipschitz_comp
    {E G H : Type*} [PseudoMetricSpace E] [PseudoMetricSpace G] [PseudoMetricSpace H]
    (f : E → G) (g : G → H) (x : E)
    (hf : ∃ K : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith K f s)
    (hg : ∃ K : NNReal, ∃ s ∈ 𝓝 (f x), LipschitzOnWith K g s) :
    ∃ K : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith K (fun y => g (f y)) s := by
  obtain ⟨Kf, s, hs, hfl⟩ := hf
  obtain ⟨Kg, t, ht, hgl⟩ := hg
  have hc : ContinuousAt f x := hfl.continuousOn.continuousAt hs
  refine ⟨Kg*Kf, s ∩ f⁻¹' t, inter_mem hs (hc ht), ?_⟩
  exact hgl.comp (hfl.mono Set.inter_subset_left)
    ((Set.mapsTo_preimage f t).mono_left Set.inter_subset_right)

theorem local_lipschitz_prodMk
    {E G H : Type*} [PseudoMetricSpace E] [PseudoMetricSpace G] [PseudoMetricSpace H]
    (f : E → G) (g : E → H) (x : E)
    (hf : ∃ K : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith K f s)
    (hg : ∃ K : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith K g s) :
    ∃ K : NNReal, ∃ s ∈ 𝓝 x,
      LipschitzOnWith K (fun y => (f y, g y)) s := by
  obtain ⟨Kf, s, hs, hfl⟩ := hf
  obtain ⟨Kg, t, ht, hgl⟩ := hg
  exact ⟨max Kf Kg, s ∩ t, inter_mem hs ht,
    (hfl.mono Set.inter_subset_left).prodMk (hgl.mono Set.inter_subset_right)⟩

theorem local_lipschitz_mul
    {E 𝕜 : Type*} [PseudoMetricSpace E] [RCLike 𝕜]
    (f g : E → 𝕜) (x : E)
    (hf : ∃ K : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith K f s)
    (hg : ∃ K : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith K g s) :
    ∃ K : NNReal, ∃ s ∈ 𝓝 x,
      LipschitzOnWith K (fun y => f y*g y) s := by
  have hm : ContDiffAt ℝ 1 (fun p : 𝕜 × 𝕜 => p.1*p.2) (f x, g x) := by
    fun_prop
  exact local_lipschitz_comp (fun y => (f y, g y))
    (fun p : 𝕜 × 𝕜 => p.1*p.2) x
    (local_lipschitz_prodMk f g x hf hg) hm.exists_lipschitzOnWith

theorem local_lipschitz_add
    {E 𝕜 : Type*} [PseudoMetricSpace E] [RCLike 𝕜]
    (f g : E → 𝕜) (x : E)
    (hf : ∃ K : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith K f s)
    (hg : ∃ K : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith K g s) :
    ∃ K : NNReal, ∃ s ∈ 𝓝 x,
      LipschitzOnWith K (fun y => f y+g y) s := by
  have hm : ContDiffAt ℝ 1 (fun p : 𝕜 × 𝕜 => p.1+p.2) (f x, g x) := by
    fun_prop
  exact local_lipschitz_comp (fun y => (f y, g y))
    (fun p : 𝕜 × 𝕜 => p.1+p.2) x
    (local_lipschitz_prodMk f g x hf hg) hm.exists_lipschitzOnWith

theorem local_lipschitz_complex_mk
    {E : Type*} [PseudoMetricSpace E]
    (f g : E → ℝ) (x : E)
    (hf : ∃ K : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith K f s)
    (hg : ∃ K : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith K g s) :
    ∃ K : NNReal, ∃ s ∈ 𝓝 x,
      LipschitzOnWith K (fun y => Complex.mk (f y) (g y)) s := by
  have hm : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => Complex.mk p.1 p.2) (f x, g x) := by
    convert Complex.equivRealProdCLM.symm.contDiff.contDiffAt using 1
    ext p
    apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply]
  exact local_lipschitz_comp (fun y => (f y, g y))
    (fun p : ℝ × ℝ => Complex.mk p.1 p.2) x
    (local_lipschitz_prodMk f g x hf hg) hm.exists_lipschitzOnWith

theorem local_lipschitz_of_eventuallyEq
    {E G : Type*} [PseudoMetricSpace E] [PseudoMetricSpace G]
    (f g : E → G) (x : E) (heq : f =ᶠ[𝓝 x] g)
    (hg : ∃ K : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith K g s) :
    ∃ K : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith K f s := by
  obtain ⟨K, s, hs, hgl⟩ := hg
  refine ⟨K, s ∩ {y | f y = g y}, inter_mem hs heq, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy w hw
  rw [hy.2, hw.2]
  exact hgl.dist_le_mul y hy.1 w hw.1

end SpringerLean

#print axioms SpringerLean.local_lipschitz_mul
