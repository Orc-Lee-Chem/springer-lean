import SpringerLean.Round2141DiskEmbeddingImprovement
import SpringerLean.Round2139ExtremalDiskEmbedding

open Set Metric Filter Function
open scoped Topology Pointwise

namespace SpringerLean

private theorem exists_holomorphic_disk_embedding_of_squareRootBranches
    {U : Set ℂ} (hU : IsOpen U) (hproper : U ≠ univ) (hroot : HasHolomorphicSquareRootBranches U)
    {x : ℂ} (hx : x ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ MapsTo f U (ball 0 1) ∧
      InjOn f U ∧ f x = 0 := by
  obtain ⟨a,ha⟩ := (ne_univ_iff_exists_notMem U).mp hproper
  let q := fun z : ℂ => z-a
  obtain ⟨g,hgd,hg⟩ :=
    hroot q (differentiable_id.sub_const a).differentiableOn
      (fun z hz => sub_ne_zero.mpr (ne_of_mem_of_not_mem hz ha))
  have hg0 (z : ℂ) (hz : z ∈ U) : g z ≠ 0 := by
    intro h
    have he : g z^2 = z-a := hg hz
    rw [h,zero_pow (by norm_num : (2:ℕ) ≠ 0)] at he
    exact ha ((sub_eq_zero.mp he.symm) ▸ hz)
  have hgI : InjOn g U := by
    intro z hz w hw he
    have hz' : g z^2 = z-a := hg hz
    have hw' : g w^2 = w-a := hg hw
    rw [he,hw'] at hz'
    linear_combination -hz'
  have hdisj (z : ℂ) (hz : z ∈ U) (w : ℂ) (hw : w ∈ U) : g z + g w ≠ 0 := by
    intro h
    have hneg := eq_neg_iff_add_eq_zero.mpr h
    have h1 : g z^2 = z-a := hg hz
    have h2 : g w^2 = w-a := hg hw
    rw [hneg,neg_sq,h2] at h1
    have he : w = z := by linear_combination h1
    rw [he] at h
    exact hg0 z hz (by linear_combination h/2)
  have hA := hgd.analyticAt (hU.mem_nhds hx)
  have hn := deriv_ne_zero_of_differentiableOn_injOn hU hgd hgI hx
  have hN : g '' U ∈ 𝓝 (g x) := by
    rw [←hA.hasStrictDerivAt.map_nhds_eq hn]
    exact image_mem_map (hU.mem_nhds hx)
  have hNc : (g '' U)ᶜ ∈ 𝓝 (-g x) := by
    rw [nhds_neg,Filter.mem_neg]
    filter_upwards [hN] with w hw
    obtain ⟨z,hz,rfl⟩ := hw
    rintro ⟨v,hv,he⟩
    exact hdisj v hv z hz (by rw [he]; simp)
  obtain ⟨ε,hε,hε'⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hNc
  have hnorm (z : ℂ) (hz : z ∈ U) : ε < ‖g z + g x‖ := by
    by_contra! h
    exact (hε' (show g z ∈ closedBall (-g x) ε by
      simpa only [mem_closedBall,dist_eq_norm,sub_neg_eq_add] using h)) ⟨z,hz,rfl⟩
  let p := fun z : ℂ => (ε:ℂ)/(g z+g x)
  have hd : DifferentiableOn ℂ p U := by
    unfold p
    exact DifferentiableOn.div (differentiableOn_const (c := (ε:ℂ)))
      (hgd.add_const _) (fun z hz => hdisj z hz x hx)
  have hm : MapsTo p U (ball 0 1) := by
    intro z hz
    change (ε:ℂ)/(g z+g x) ∈ ball 0 1
    rw [mem_ball_zero_iff,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
    exact (div_lt_one₀ (norm_pos_iff.mpr (hdisj z hz x hx))).mpr (hnorm z hz)
  have hi : InjOn p U := by
    intro z hz w hw he
    have hε0 : (ε:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
    have h : (g z+g x)⁻¹ = (g w+g x)⁻¹ :=
      mul_left_cancel₀ hε0 (by simpa only [p,div_eq_mul_inv] using he)
    exact hgI hz hw (add_right_cancel (inv_injective h))
  let f := diskMobius (p x) ∘ p
  have hpx := hm hx
  exact ⟨f,(diskMobius_differentiableOn hpx).comp hd hm,
    (diskMobius_mapsTo hpx).comp hm,(diskMobius_injOn hpx).comp hi hm,diskMobius_at_parameter _⟩

/-- Analytic form of the Riemann mapping theorem with the square-root
branch property as its topological input. -/
theorem exists_holomorphic_disk_bijOn_of_squareRootBranches
    {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) (hproper : U ≠ univ)
    (hroot : HasHolomorphicSquareRootBranches U) {x : ℂ} (hx : x ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ BijOn f U (ball 0 1) ∧ f x = 0 := by
  obtain ⟨f,hd,hm,hi,h0,hmax⟩ := exists_extremal_holomorphic_disk_embedding hU hc hx
    (exists_holomorphic_disk_embedding_of_squareRootBranches hU hproper hroot hx)
  have hs : SurjOn f U (ball 0 1) := by
    by_contra hn
    obtain ⟨g,hgd,hgm,hgi,hg0,hgt⟩ := improve_holomorphic_disk_embedding hU hroot hx f hd hm hi h0 hn
    exact (not_lt_of_ge (hmax g hgd hgm hgi hg0)) hgt
  exact ⟨f,hd,⟨hm,hi,hs⟩,h0⟩

/-- Riemann mapping theorem on a proper simply connected plane domain,
with the base point carried to zero. -/
theorem riemannMapping_bijOn_unitDisk
    {U : Set ℂ} (hU : IsOpen U) (hc : IsSimplyConnected U) (hproper : U ≠ univ)
    {x : ℂ} (hx : x ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ BijOn f U (ball 0 1) ∧ f x = 0 :=
  exists_holomorphic_disk_bijOn_of_squareRootBranches hU hc.isPathConnected.isConnected.isPreconnected
    hproper (hasHolomorphicSquareRootBranches_of_isSimplyConnected hU hc) hx

end SpringerLean
