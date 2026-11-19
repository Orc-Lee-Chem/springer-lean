import SpringerLean.Round1662EnergyLocalCostLedger

namespace SpringerLean

/-- Pure signed assembly of the P, R, and S fluxes. This preserves both
the chi-sigma drift and the 2f-b chi' radial cancellation. -/
theorem energyFlux_signed_ledger
    (K χ f σ t cp fp p2 u drift ur yr yOverR
      ugrad sigmaGrad ctrace lap P R S : ℝ)
    (hK : 1 < K)
    (hP : P = χ*p2+χ*lap-
      cp*(K*u*ur+t*ugrad))
    (hR : R = (yOverR*f-(f+t*fp)*yr-K*fp)*u^2+
      2*f*u*ur)
    (hS : S = 2*σ*drift+sigmaGrad-2*σ*ctrace)
    (hPDE : χ*lap-4*(K-1)*σ*drift =
      4*(K-1)*(χ-σ)*drift-4*K*(K-1)*χ*u^2) :
    let b := K/(4*(K-1))
    b*(P+4*(K-1)*R-2*(K-1)*S) =
      b*χ*p2-K^2*(χ+fp)*u^2+
      K*(χ-σ)*drift+
      K*(2*f-b*cp)*u*ur-
      K*(f+t*fp)*yr*u^2+
      K*yOverR*f*u^2-
      b*cp*t*ugrad-
      (K/2)*sigmaGrad+K*σ*ctrace := by
  have hKm1 : K-1 ≠ 0 := by linarith
  dsimp only
  calc
    (K/(4*(K-1)))*(P+4*(K-1)*R-2*(K-1)*S) =
      (K/(4*(K-1)))*
        (χ*p2+(χ*lap-4*(K-1)*σ*drift)-
          cp*(K*u*ur+t*ugrad)+4*(K-1)*R-
          2*(K-1)*(sigmaGrad-2*σ*ctrace)) := by
            rw [hP,hS]
            ring
    _ = (K/(4*(K-1)))*
        (χ*p2+(4*(K-1)*(χ-σ)*drift-
          4*K*(K-1)*χ*u^2)-
          cp*(K*u*ur+t*ugrad)+4*(K-1)*R-
          2*(K-1)*(sigmaGrad-2*σ*ctrace)) := by
            rw [hPDE]
    _ = _ := by
      rw [hR]
      field_simp [hKm1]
      ring

end SpringerLean

#print axioms SpringerLean.energyFlux_signed_ledger
