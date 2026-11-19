import SpringerLean.Round2098CorrectedLogFromGreenComparison
import SpringerLean.Round2044EvenStarRotatedSimilarity
import SpringerLean.Round2092OddActualFactorCounterexamples

open MeasureTheory Set Polynomial Real

namespace SpringerLean

noncomputable def evenStarRadius (k : ℕ) : ℝ := (2:ℝ)^(1/(k:ℝ))

theorem evenStarRadius_pos (k : ℕ) : 0 < evenStarRadius k := Real.rpow_pos_of_pos (by norm_num) _

theorem evenStarRadius_pow (k : ℕ) (hk : 0 < k) : evenStarRadius k ^ k = 2 := by
  simpa only [evenStarRadius,one_div] using Real.rpow_inv_natCast_pow (by norm_num : (0:ℝ) ≤ 2) hk.ne'

theorem evenStarRadius_pow_double (k : ℕ) (hk : 0 < k) : evenStarRadius k^(2*k) = 4 := by
  rw [show 2*k=k*2 by omega, pow_mul, evenStarRadius_pow k hk]
  norm_num

theorem evenStar_omitted_norm_le_radius
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F) (hK : EvenGeneratorInvariant K k)
    (hIm : F '' exteriorDisk = Kᶜ) (z : ℂ) (hz : z ∈ K) : ‖z‖ ≤ evenStarRadius k := by
  let G := evenExteriorPowerQuotient F k
  have hG := evenExteriorPowerQuotient_actual_centered F K k hk hF hK hIm
  have hgeom := (evenExteriorPowerQuotient_actual_geometry F K k hk hF hK hIm).2.1
  have hmem : z^k ∈ exteriorOmitted G := by
    change z^k ∈ (G '' exteriorDisk)ᶜ
    rw [hgeom,compl_compl]
    exact mem_image_of_mem _ hz
  have hle := exteriorOmitted_norm_le_two G hG hmem
  rw [norm_pow, ← evenStarRadius_pow k hk] at hle
  exact le_of_pow_le_pow_left₀ hk.ne' (evenStarRadius_pos k).le hle

theorem evenStar_regular_mem_norm_le_radius (k : ℕ) (hk : 0 < k) (z : ℂ)
    (hz : z ∈ regularStarRaySet (2*k)) : ‖z‖ ≤ evenStarRadius k := by
  obtain ⟨r,hr,hp,η,hη,rfl⟩ := hz
  have hn := Complex.norm_eq_one_of_pow_eq_one hη (by omega : 2*k ≠ 0)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,hn,mul_one]
  rw [← evenStarRadius_pow_double k hk] at hp
  exact le_of_pow_le_pow_left₀ (by omega : 2*k ≠ 0) (evenStarRadius_pos k).le hp

theorem evenStar_farthestDistance_le_of_radius
    (K : Set ℂ) (hK : IsCompact K) (hn : K.Nonempty) (a : ℝ)
    (hb : ∀ v ∈ K, ‖v‖ ≤ a) (z : ℂ) : continuumFarthestDistance K z ≤ a+‖z‖ := by
  obtain ⟨v,hv,he⟩ := continuumFarthestDistance_eq_distance_at_max K hK hn z
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [hb v hv])

/-- For the regular even star the opposite tip realizes the radius bound. -/
theorem evenStar_regular_farthestDistance
    (k : ℕ) (hk : 0 < k) (z : ℂ) (hz : z ∈ regularStarRaySet (2*k)) :
    continuumFarthestDistance (regularStarRaySet (2*k)) z = evenStarRadius k+‖z‖ := by
  let a := evenStarRadius k
  let K := regularStarRaySet (2*k)
  have hK : IsCompact K := by
    change IsCompact (regularStarRaySet (2*k))
    rw [← oddStarPerturbation_zero_omitted_eq_regularStarRays (2*k) (by omega)]
    exact oddStarPerturbation_omitted_isCompact (2*k) (by omega) 0 (by norm_num)
  apply le_antisymm (evenStar_farthestDistance_le_of_radius K hK ⟨z,hz⟩ a
    (evenStar_regular_mem_norm_le_radius k hk) z)
  obtain ⟨r,hr,_,η,hη,he⟩ := hz
  have hηn := Complex.norm_eq_one_of_pow_eq_one hη (by omega : 2*k ≠ 0)
  have hopp : (-η)^(2*k) = 1 := by
    rw [pow_mul,neg_sq,← pow_mul,hη]
  have hv : (a:ℂ)*(-η) ∈ K :=
    ⟨a,(evenStarRadius_pos k).le,(evenStarRadius_pow_double k hk).le,-η,hopp,rfl⟩
  have hd := continuumFarthestDistance_ge_distance K hK z _ hv
  rw [he, show (r:ℂ)*η-(a:ℂ)*(-η) = ((r+a:ℝ):ℂ)*η by push_cast; ring] at hd
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg hr (evenStarRadius_pos k).le),hηn,mul_one] at hd
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,hηn,mul_one,add_comm]
  exact hd

theorem evenStar_log_radius_add_norm_eq_corrected
    (k : ℕ) (hk : 0 < k) (z : ℂ) :
    log (evenStarRadius k+‖z‖) = log (evenStarRadius k) +
      evenStarCorrectedRadialTest k ‖z^k‖ + ‖z^k‖^2/(64*(k:ℝ)^2) := by
  let a := evenStarRadius k
  have ha : 0 < a := evenStarRadius_pos k
  have h := Real.pow_rpow_inv_natCast (norm_nonneg z) hk.ne'
  have hr : (‖z^k‖/2)^(1/(k:ℝ)) = ‖z‖/a := by
    rw [Real.div_rpow (norm_nonneg _) (by norm_num), norm_pow, one_div, h]
    simp [a,evenStarRadius,one_div]
  rw [evenStarCorrectedRadialTest, abs_of_nonneg (norm_nonneg _), hr]
  have hfactor : a + ‖z‖ = a * (1 + ‖z‖/a) := by
    field_simp [ha.ne'] <;> ring
  rw [hfactor, Real.log_mul ha.ne' (by positivity)]
  ring

end SpringerLean
