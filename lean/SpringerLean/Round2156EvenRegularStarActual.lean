import SpringerLean.Round2155SphereComplementUniformization

open Set Real

namespace SpringerLean

/-- The even star theorem for an arbitrary nondegenerate plane
continuum, with the actual normalization supplied by the proof. -/
theorem evenRegularStar_factorConstant_actual
    (K : Set ℂ) (hK : IsCompact K) (hc : IsConnected K) (k : ℕ) (hk : 0 < k)
    (c : ℂ) (hrot : EvenGeneratorInvariant (continuumTranslate K (-c)) k)
    (u v : ℂ) (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v) :
    let S := regularStarRaySet (2*k)
    ∃ (r : ℝ) (F : ℂ → ℂ), 0 < r ∧ CenteredExteriorUnivalent F ∧
      F '' exteriorDisk = (continuumScale (continuumFill (continuumTranslate K (-c))) (r:ℂ))ᶜ ∧
      factorConstant K ≤ factorConstant S ∧
      (1-(k:ℝ)^2*‖exteriorForwardCoeff F (2*k-1)‖^2)/(96*(k:ℝ)^2) ≤
        log (factorConstant S/factorConstant K) ∧
      (factorConstant K = factorConstant S ↔
        ∃ b d : ℂ, b ≠ 0 ∧ K = continuumTranslate (continuumScale S b) d) := by
  let T := continuumTranslate K (-c)
  let S := regularStarRaySet (2*k)
  let u' := u+(-c)
  let v' := v+(-c)
  have hcont : Continuous (fun z : ℂ => z+(-c)) := continuous_id.add continuous_const
  have hTc : IsCompact T := hK.image hcont
  have hTconn : IsConnected T := hc.image _ hcont.continuousOn
  have hu' : u' ∈ T := ⟨u,hu,rfl⟩
  have hv' : v' ∈ T := ⟨v,hv,rfl⟩
  have hne : u' ≠ v' := fun h => huv (add_right_cancel h)
  have hsub := subset_continuumFill T
  have hU (a : ℂ) (ha : a ∈ continuumFill T) : Nonempty (ReciprocalDiskUniformization T a) := by
    by_cases he : a = u'
    · exact reciprocalDiskUniformization_exists T hTc hTconn a v' ha (hsub hv')
        (fun h => hne (he.symm.trans h))
    · exact reciprocalDiskUniformization_exists T hTc hTconn a u' ha (hsub hu') he
  obtain ⟨r,F,hr,hF,hIm,hle,hgap,heq⟩ :=
    evenContinuum_factorConstant_of_reciprocalDiskUniformization T hTc hTconn k hk hrot u' v' hu' hv' hne hU
  have hf : factorConstant T = factorConstant K := factorConstant_translate K (-c)
  rw [hf] at hle hgap heq
  refine ⟨r,F,hr,hF,hIm,hle,hgap,?_⟩
  constructor
  · intro h
    obtain ⟨b,hb,hT⟩ := heq.mp h
    have hbck : continuumTranslate T c = K := by
      simpa only [T,neg_neg] using continuumTranslate_translate_neg K (-c)
    exact ⟨b,c,hb,hbck.symm.trans (congrArg (fun A => continuumTranslate A c) hT)⟩
  · rintro ⟨b,d,hb,rfl⟩
    exact factorConstant_similarity S b d hb

/-- Rotation about the specified center by (2π/m) preserves the set. -/
def ContinuumRotationInvariant (K : Set ℂ) (m : ℕ) (c : ℂ) : Prop :=
  let ζ := Complex.exp (2*Real.pi*Complex.I/(m:ℂ))
  ∀ z ∈ K, c+ζ*(z-c) ∈ K

theorem continuumTranslate_evenGeneratorInvariant
    (K : Set ℂ) (k : ℕ) (c : ℂ) (hrot : ContinuumRotationInvariant K (2*k) c) :
    EvenGeneratorInvariant (continuumTranslate K (-c)) k := by
  rintro _ ⟨z,hz,rfl⟩
  let ζ := Complex.exp (2*Real.pi*Complex.I/((2*k:ℕ):ℂ))
  refine ⟨c+ζ*(z-c),hrot z hz,?_⟩
  change c+ζ*(z-c)+(-c) = ζ*(z+(-c))
  ring

/-- The universal star comparison holds exactly for even rotational
orders among integers at least two. -/
theorem regularStar_universal_factorConstant_iff_even (m : ℕ) (hm : 2 ≤ m) :
    (∀ K : Set ℂ, IsCompact K → IsConnected K →
      (∃ u v : ℂ, u ∈ K ∧ v ∈ K ∧ u ≠ v) →
      ∀ c : ℂ, ContinuumRotationInvariant K m c →
        factorConstant K ≤ factorConstant (regularStarRaySet m)) ↔ Even m := by
  constructor
  · intro h
    by_contra hne
    have ho : Odd m := Nat.not_even_iff_odd.mp hne
    have hm3 : 3 ≤ m := by obtain ⟨n,hn⟩ := ho; omega
    obtain ⟨K,hK,hc,hn,hr,hs⟩ := odd_regularStar_factorConstant_counterexample m hm3 ho
    let ζ := Complex.exp (2*Real.pi*Complex.I/(m:ℂ))
    have hζ : ζ ^ m = 1 := (Complex.isPrimitiveRoot_exp m (by omega)).pow_eq_one
    have hsym : ContinuumRotationInvariant K m 0 := by
      intro z hz
      simpa only [zero_add,sub_zero] using (hr ζ z hζ).mpr hz
    exact (not_le_of_gt hs) (h K hK hc hn 0 hsym)
  · rintro ⟨k,hk⟩ K hK hc ⟨u,v,hu,hv,huv⟩ c hrot
    have hp : 0 < k := by omega
    subst m
    rw [←two_mul] at hrot ⊢
    obtain ⟨_,_,_,_,_,hle,_,_⟩ := evenRegularStar_factorConstant_actual K hK hc k hp c
      (continuumTranslate_evenGeneratorInvariant K k c hrot) u v hu hv huv
    exact hle

end SpringerLean
