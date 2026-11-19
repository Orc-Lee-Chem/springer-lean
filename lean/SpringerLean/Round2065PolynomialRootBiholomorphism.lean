import SpringerLean.Round2064PolynomialAnalyticRoot
import SpringerLean.Round2045PolynomialExteriorFibers
import SpringerLean.Round2029ExteriorMapUniqueness

open Polynomial Set Filter Metric
open scoped Topology

namespace SpringerLean

/-- An analytic polynomial root coordinate on the full exterior is
biholomorphic. Properness and openness give surjectivity, then the
algebraic exhaustion of every polynomial fiber gives injectivity. -/
theorem polynomial_exterior_root_biholomorphic
    (Q : ℂ[X]) (hn : 0 < Q.natDegree) (B : ℂ → ℂ)
    (hB : AnalyticOnNhd ℂ B {z : ℂ | 1 < ‖Q.eval z‖})
    (hpow : ∀ z : ℂ, 1 < ‖Q.eval z‖ → (B z)^Q.natDegree = Q.eval z) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F exteriorDisk ∧
      Set.InjOn F exteriorDisk ∧
      (∀ w ∈ exteriorDisk, Q.eval (F w) = w ^ Q.natDegree) ∧
      (∀ w ∈ exteriorDisk, B (F w) = w) ∧
      (∀ z : ℂ, 1 < ‖Q.eval z‖ → F (B z) = z) := by
  classical
  let Ω : Set ℂ := {z | 1 < ‖Q.eval z‖}
  have hΩ : IsConnected Ω := polynomial_unit_lemniscate_exterior_isConnected Q hn
  have hΩO : IsOpen Ω := isOpen_lt continuous_const Q.continuous.norm
  have hBext (z : ℂ) (hz : z ∈ Ω) : B z ∈ exteriorDisk := by
    change 1 < ‖B z‖
    by_contra! hz'
    have hp := pow_le_one₀ (norm_nonneg (B z)) hz' (n := Q.natDegree)
    rw [← norm_pow, hpow z hz] at hp
    exact (not_lt_of_ge hp) hz
  let b : Ω → exteriorDisk := fun z => ⟨B z, hBext z z.2⟩
  let q : Ω → exteriorDisk := fun z => ⟨Q.eval z, z.2⟩
  let power : exteriorDisk → exteriorDisk := fun z => ⟨(z : ℂ)^Q.natDegree, by
    change 1 < ‖(z : ℂ)^Q.natDegree‖
    rw [norm_pow]
    exact one_lt_pow₀ z.2 hn.ne'⟩
  have hproperq : IsProperMap q :=
    (Q.isProperMap_eval ((natDegree_pos_iff_degree_pos).mp hn)).restrictPreimage exteriorDisk
  have hcB : Continuous b := hB.continuousOn.restrict.subtype_mk _
  have hcP : Continuous power := (continuous_subtype_val.pow _).subtype_mk _
  have heq : power ∘ b = q := by
    funext z
    exact Subtype.ext (hpow z z.2)
  have hproperb : IsProperMap b :=
    isProperMap_of_comp_of_t2 hcB hcP (heq.symm ▸ hproperq)
  have hnconst : ¬∃ w : ℂ, ∀ z ∈ Ω, B z = w := by
    rintro ⟨w, hw⟩
    obtain ⟨z₂,hz₂⟩ := IsAlgClosed.eval_surjective hn.ne' (2 : ℂ)
    obtain ⟨z₃,hz₃⟩ := IsAlgClosed.eval_surjective hn.ne' (3 : ℂ)
    change Q.eval z₂ = 2 at hz₂
    change Q.eval z₃ = 3 at hz₃
    have hz₂Ω : z₂ ∈ Ω := by change 1 < ‖Q.eval z₂‖; rw [hz₂]; norm_num
    have hz₃Ω : z₃ ∈ Ω := by change 1 < ‖Q.eval z₃‖; rw [hz₃]; norm_num
    have h2 := hpow z₂ hz₂Ω
    have h3 := hpow z₃ hz₃Ω
    rw [hw z₂ hz₂Ω, hz₂] at h2
    rw [hw z₃ hz₃Ω, hz₃] at h3
    have h23 := h2.symm.trans h3
    norm_num at h23
  have hOpen : IsOpen (B '' Ω) :=
    ((hB.is_constant_or_isOpen hΩ.isPreconnected).resolve_left hnconst)
      Ω Subset.rfl hΩO
  have hRange : range b = Subtype.val ⁻¹' (B '' Ω) := by
    ext w
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨z,z.2,rfl⟩
    · rintro ⟨z,hz,he⟩
      exact ⟨⟨z,hz⟩, Subtype.ext he⟩
  have hCl : IsClopen (range b) := ⟨hproperb.isClosed_range, hRange.symm ▸
    hOpen.preimage continuous_subtype_val⟩
  have hConn : IsConnected exteriorDisk := complex_norm_gt_isConnected 1 (by norm_num)
  have : PreconnectedSpace exteriorDisk := Subtype.preconnectedSpace hConn.isPreconnected
  have hSurj : Function.Surjective b := by
    rcases isClopen_iff.mp hCl with he | hf
    · obtain ⟨x,hx⟩ := hΩ.nonempty
      have hmem := mem_range_self (f := b) ⟨x,hx⟩
      simp [he] at hmem
    · exact range_eq_univ.mp hf
  let F (w : ℂ) := if hw : w ∈ exteriorDisk then ((hSurj ⟨w,hw⟩).choose : ℂ) else 0
  have hFΩ (w : ℂ) (hw : w ∈ exteriorDisk) : F w ∈ Ω := by
    simpa only [F, dite_eq_left hw] using ((hSurj ⟨w,hw⟩).choose).2
  have hright (w : ℂ) (hw : w ∈ exteriorDisk) : B (F w) = w := by
    simpa only [F, dite_eq_left hw] using congrArg Subtype.val (hSurj ⟨w,hw⟩).choose_spec
  have hFinj : Set.InjOn F exteriorDisk := fun w hw v hv he =>
    (hright w hw).symm.trans ((congrArg B he).trans (hright v hv))
  have hId (w : ℂ) (hw : w ∈ exteriorDisk) : Q.eval (F w) = w ^ Q.natDegree := by
    rw [← hpow (F w) (hFΩ w hw), hright w hw]
  have hFimage : F '' exteriorDisk = Ω := polynomial_exterior_image_eq Q hn F hFinj hId
  have hleft (z : ℂ) (hz : z ∈ Ω) : F (B z) = z := by
    have hz' : z ∈ F '' exteriorDisk := hFimage.symm ▸ hz
    obtain ⟨w,hw,rfl⟩ := hz'
    rw [hright w hw]
  have hBinj : Set.InjOn B Ω := fun z hz w hw he =>
    (hleft z hz).symm.trans ((congrArg F he).trans (hleft w hw))
  refine ⟨F, ?_, hFinj, hId, hright, hleft⟩
  intro w hw
  let z := F w
  have hz : z ∈ Ω := hFΩ w hw
  have han := hB z hz
  have hd : deriv B z ≠ 0 := deriv_ne_zero_of_differentiableOn_injOn
    hΩO hB.differentiableOn hBinj hz
  let I := han.hasStrictDerivAt.localInverse B (deriv B z) z hd
  have hI0 : I (B z) = z :=
    HasStrictFDerivAt.localInverse_apply_image
      (han.hasStrictDerivAt.hasStrictFDerivAt_equiv hd)
  have hI : AnalyticAt ℂ I w := (hright w hw) ▸ han.analyticAt_localInverse hd
  have hIin : ∀ᶠ v in 𝓝 w, I v ∈ Ω := by
    apply hI.continuousAt.eventually
    rw [← hright w hw, hI0]
    exact hΩO.mem_nhds hz
  have hIright : ∀ᶠ v in 𝓝 w, B (I v) = v :=
    (hright w hw) ▸ han.hasStrictDerivAt.eventually_right_inverse hd
  apply hI.congr
  filter_upwards [exteriorDisk_isOpen.mem_nhds hw, hIin, hIright] with v hv hIv hrv
  exact hBinj hIv (hFΩ v hv) (hrv.trans (hright v hv).symm)

end SpringerLean
