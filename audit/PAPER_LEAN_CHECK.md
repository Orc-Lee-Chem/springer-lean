# Paper-to-Lean crosswalk

This crosswalk uses the 37-page manuscript in [`paper/main.pdf`](../paper/main.pdf) and the [complete TeX](../paper/main.tex). The paper and the historical Lean freeze have separate provenance. The [paper statements](../lean/PaperStatementsAudit.lean) are byte-identical to the single-ramp freeze. The release retains every project module in the frozen theorem-dependency graph and their source import closure. The root omits the independent `PaperMomentLimitStatements` wrapper. The full Lean output for all 15 public declarations is in [`frozen-paper-statements.txt`](frozen-paper-statements.txt).

## Large-order inverse coefficients

Theorem 1 (p. 2, `thm:large`) is [`SpringerLean.PaperStatementsAudit.theorem_1_1_large_751_singleRamp`](../lean/PaperStatementsAudit.lean#L7). The exterior class consists of a holomorphic injection on `{z : |z| > 1}` with analytic, constant-free correction `F(1/t) − 1/t` at zero. `exteriorInverse` is the actual inverse on the image of that disk, and `exteriorInverseCoeff` takes the coefficient of `1/t − exteriorInverse F (1/t)`. Equality uses `Set.EqOn` on the entire open exterior disk.

| Manuscript location | Formal proof and correspondence |
| --- | --- |
| `eq:signed-fill`, `eq:signed-energy` and (3), `eq:signed-criterion` | `SpringerLean.exteriorInverseCoeff_odd_eq_actualHarmonic_diskIntegral` and `SpringerLean.exists_actualHarmonicPhaseEnergy_identity` work with the actual harmonic filling and normalized disk area. `SpringerLean.AnalyticRevision.exteriorInverseCoeff_exists_singleRamp_signed_bound` pays `3/14` times the phase potential and half the omitted-set moment. Its body uses `SpringerLean.AnalyticRevision.actualHarmonicPhase_energy_le_seven_thirds`. |
| Lemmas 2–3, especially p. 7, (13), `eq:gaussian-single-end-cost` | The paper first bounds `n |B_n|` by the actual radial boundary moment using the residue identity and the radial limit. The trace lies in the omitted set almost everywhere. The pointwise affine-platform majorant on its convex hull gives the middle inequality. The fixed-direction convex projection theorem applied to the same trace gives the last line. In Lean, `SpringerLean.exteriorOmitted_candidate_second_radius_gt_39_20` uses `SpringerLean.exteriorInverseCoeff_le_affinePlatform_cost`, whose singleton case of `SpringerLean.exteriorInverseCoeff_mul_norm_le_of_finite_convex_caps` applies the convex comparison on smooth dilates. The omitted-set cap transfers with an arbitrarily small error, and the scaled actual inverse coefficient tends to the original one. This is an equivalent route to the first-to-last inequality of (13). Both routes use the same selected endpoint, affine test and normalized circle average. |
| `eq:chord-arc-exact`, `eq:actual-joint-J` and `lem:cutoff` | `SpringerLean.refinedAffineSmoothPower_moving_Jensen` bounds the Jensen term using the difference of third moments, `E[S³] − (E[S])³`. The conclusions are used on the same selected pair by `SpringerLean.exteriorInverseCoeff_candidate_selected_joint_J` and `SpringerLean.exteriorInverseCoeff_candidate_selected_two_fine_widths`. |
| Lemma 5, pp. 12–13, `lem:actual-disk-gain` | The manuscript passes the boundary capped convex order through Poisson smoothing and uses the test `(x − M(r))₊` to obtain a cap at each angle. `SpringerLean.actualHarmonic_flattened_peak_cap` instead applies the regularized Poisson-weighted inequality and rotates the resulting central cap to each angle. The peak and normalization agree. `SpringerLean.actualHarmonic_inner_positivePower_le_clippedModel` and `SpringerLean.actualHarmonic_positivePower_unitDisk_cubic_gain_of_radius` then yield the strict disk gain used by the final proof. |
| `eq:tiny-cutoff`, `eq:model-error` and `eq:true-axis-corrected` | `SpringerLean.AnalyticRevision.actualSignedPhaseIntegral_tiny_first_strict` treats tiny deficit. `SpringerLean.AnalyticRevision.actualSignedPhaseDensity_aligned_le_twoPower` and `SpringerLean.AnalyticRevision.actualSignedPhaseDensity_trueAxis_lt_lower_power` compare the actual signed densities pointwise. `SpringerLean.AnalyticRevision.actualSignedPhaseIntegral_lt_two_reference` combines the branches. The disk expectation in the paper uses the semicircle law of `2 Re Z` for normalized area in the unit disk. |
| Lemma 9, p. 19, `lem:actual-phase-energy` | `SpringerLean.AnalyticRevision.rampFlux` uses the capped linear function and `SingleRamp.clippedLinearFlux` handles both scalar branches, with a rescaling of the quadratic test in Lean. `SpringerLean.AnalyticRevision.cutFlux_integral_le` integrates the a.e. pointwise inequality using the cutoff. The full-disk conclusion has only the original exterior-class, order, and unit-phase hypotheses. |
| Theorem 1, equality | `SpringerLean.AnalyticRevision.exteriorInverseCoeff_large_lt_catalan_of_nonslit` excludes all nonslits, and `SpringerLean.exteriorInverseCoeff_sharp_of_eqOn_slit_all_orders` gives the converse for every unit slit. |

The energy and large-order proof-body paths are covered by the included declaration checker. The transitive project graph excludes the historical endpoint table and energy theorem. The manuscript’s explicit quadratic and scalar estimates supply the paper-side comparisons.

## Actual radial boundary moments

Theorems 10 and 13 (pp. 22 and 25, `thm:moments` and `thm:radial-continuous`). The Lean statements integrate the a.e. limit of the actual map against `dt/(2π)`, use `D = 1 − |b₁|²` for the forward coefficient, and use `Γ(p+1)/Γ(1+p/2)²` for the slit constant.

| Manuscript location | Formal proof and correspondence |
| --- | --- |
| `lem:trace` and `eq:rad-area` | `SpringerLean.actualExteriorRadialTrace_ae_tendsto` identifies the actual radial trace. `SpringerLean.actualBoundaryRadialMoment_circle_tendsto` passes the exterior circle integrals to that trace. The finite signed-area estimates and Parseval give the four even moments. |
| `eq:m2`, `eq:m4`, `eq:m6`, `eq:m8` | The four `theorem_9_1_…_actual_radial…` entries give the same constants and the slit equality iff. The sixth-order square identity is `SpringerLean.sixthMoment_strong_square_identity`. The eighth-order factorization is `SpringerLean.eighth_strong_residual_factor`. |
| `eq:projection-order`, `eq:h-curvature` and `eq:interpolation-bracket` | The paper can apply the published boundary projection theorem. `SpringerLean.actualExteriorRadialTrace_half_projection_localConvex_le` uses Poisson comparison and radial convergence. The compensated convex test and rational bracket bounds give the same `D/80` deficit on both closed intervals, including their endpoints. `SpringerLean.actualBoundaryRadialMoment_four_to_eight_eq_iff_slit` handles both equality directions. |

## Polynomial derivative-root moments

Proposition 14 (p. 26, `prop:zero-moments`) uses the centroid of the original polynomial and the scale `(t/|a|)^(1/n)`. Roots are multisets. The theorem covers arbitrary `n ≥ 2`, positive `t` with connected sublevel set, `0 ≤ j < n`, and real `4 ≤ p ≤ 8`.

| Manuscript step | Formal proof and correspondence |
| --- | --- |
| Normalize the polynomial and construct its exterior map | `SpringerLean.polynomialLemniscate_normalized_centered_connected` and `SpringerLean.connectedLemniscateExteriorExistence_proved` produce the actual centered exterior map and `Q(F(w)) = w^n` from the original hypotheses. |
| Root comparison, derivative comparison, strictness | `SpringerLean.polynomial_root_power_mean_le_actual_radial` uses the log-hinge comparison and actual radial limit. `SpringerLean.polynomial_iterated_derivative_root_power_mean_le` iterates the compression/Jensen bound. `SpringerLean.monicPolynomial_no_exterior_slit_identity` rules out a unit slit by the nonzero constant term. |
| Exact supremum across degrees at fixed `p,j` | `SpringerLean.connectedPolynomialDerivativeMoments_near` uses a level-one rescaling of the manuscript’s Chebyshev sequence, with the same normalized root moments and Rolle-interlacing limit. `SpringerLean.connectedPolynomialDerivativeMoments_csSup_and_not_attained` combines these witnesses with the strict upper bound. |

## Regular stars

Theorem 15 (pp. 28–29, `thm:parity` and `eq:star-quant`) covers actual nondegenerate plane continua. Rotation is about a specified center. The even-order quantitative coefficient is the forward Laurent coefficient of the capacity-normalized, centered filled continuum.

| Manuscript step | Formal proof and correspondence |
| --- | --- |
| Translate, fill and normalize | `SpringerLean.reciprocalDiskUniformization_exists` constructs the actual exterior normalization. `SpringerLean.factorConstant_fill_eq` and `SpringerLean.factorConstant_similarity` preserve the quantity built from polynomial sup norms. |
| Equilibrium pushforward and even power map | `SpringerLean.evenPowerQuotient_actual_boundary_probability_pushforward` handles the actual law, and `SpringerLean.evenExteriorPowerQuotient_firstCoeff_eq_k_mul_forwardCoeff` gives the first quotient coefficient `k b_(2k−1)`. Lean uses the radial potential directly for the factor formula, with equilibrium identification separately audited. |
| Quantitative even bound and equality | `SpringerLean.evenStarCorrectedRadialTest_integral_le_of_green_comparison` and `SpringerLean.actualBoundaryRadialMoment_two_odd_margin` produce the deficit divided by `96 k²`. The normalized and arbitrary-continuum entries establish both directions of the similarity classification. A star has empty interior, so equality for the filled set also classifies the original set. |
| Every odd `m ≥ 3` | `SpringerLean.oddStarPerturbation_centeredExteriorUnivalent` and `SpringerLean.oddStarPerturbation_actual_continuum` construct the actual symmetric continuum. `SpringerLean.oddStarOppositeTipLogDistance_integral_hasDerivAt_zero` and `SpringerLean.oddStarOppositeTipLogDistance_integral_deriv_strict_pos` give the positive variation. The odd entry gives the strict counterexample and the parity entry packages the universal iff. |

The radial projection and symmetric comparison in the paper use Baernstein–Laugesen–Pritsker, Theorem 2 and Corollary 6.3. The factor-constant formula is Pritsker–Ruscheweyh, Theorem 1.1, with capacity normalized to one. [BLP](https://doi.org/10.4310/PAMQ.2011.v7.n1.a4) [PR2](https://math.okstate.edu/people/igor/ipp2.pdf)
