# Springer coefficients, boundary moments, polynomial zeros, and regular stars

**Cheng Li** · School of Mathematical Sciences, Fudan University  
Manuscript · [English PDF](paper/main.pdf) · [Complete TeX](paper/main.tex) · [Academic homepage](https://orc-lee-chem.github.io/)

| Result | Lean entry in `SpringerLean.PaperStatementsAudit` |
| --- | --- |
| Springer’s Catalan bound for the inverse coefficient `B_(2k−1)` for every `k ≥ 751`, with equality exactly for unit slit maps on the open exterior disk | [`theorem_1_1_large_751_singleRamp`](lean/PaperStatementsAudit.lean#L7) |
| Sharp moments of the actual radial trace for every real `4 ≤ p ≤ 8`, with a quantitative deficit and slit equality. The even-order results also include `p = 2` and the stronger sixth- and eighth-moment estimates. | [`theorem_9_1_p4_to_p8_actual_radial` and even moments](lean/PaperStatementsAudit.lean#L141) |
| Strict normalized derivative-root moment bounds for polynomials with connected lemniscates for `4 ≤ p ≤ 8`. At fixed `p,j` the bound is the unattained supremum across degrees. | [`proposition_9_2_strict_derivative_zero_moment`](lean/PaperStatementsAudit.lean#L22), [`proposition_9_2_exact_supremum_and_nonattainment`](lean/PaperStatementsAudit.lean#L32) |
| Regular-star comparison precisely in even order, with a quantitative bound and similarity classification. Every odd order `m ≥ 3` has a strict continuum counterexample. | [Even, odd, and parity entries](lean/PaperStatementsAudit.lean#L69) |

[Paper-to-Lean crosswalk](audit/PAPER_LEAN_CHECK.md) · [Full types and transitive axioms](audit/frozen-paper-statements.txt) · [Paper hashes](paper/SHA256SUMS.txt) · [Fixed publication version](https://github.com/Orc-Lee-Chem/springer-lean/tree/single-ramp-v1)

[Cold-build report](audit/cold-build.json) · [Proof-dependency paths](audit/proof-routes.txt)

## Reproduce the Lean audit

Install Git, [elan](https://github.com/leanprover/elan), and Python 3. From a fresh clone, run the following in a POSIX shell. Lean is pinned to `leanprover/lean4:v4.34.1`. The [Lake lock file](lean/lake-manifest.json) pins mathlib to `d13f23b723b8a846827a245b89c10fc7d3f11612` and records all transitive revisions.

```sh
cd lean
lake env lean --version
lake exe cache get
lake env python3 ../cold_replay.py ../.audit-local --workers 1
export SPRINGER_DEPENDENCY_TSV="../.audit-local/declaration_dependencies.tsv"
lake env lean -j 1 AnalyticProofDependencies.lean
python3 ../check_analytic_dependencies.py "$SPRINGER_DEPENDENCY_TSV"
python3 ../audit/verify_output.py ../.audit-local
```

On Windows, use the Python 3 launcher from PowerShell.

```powershell
Set-Location lean
lake env lean --version
lake exe cache get
lake env py ../cold_replay.py ../.audit-local --workers 1
$env:SPRINGER_DEPENDENCY_TSV = '../.audit-local/declaration_dependencies.tsv'
lake env lean -j 1 AnalyticProofDependencies.lean
py -3 ../check_analytic_dependencies.py $env:SPRINGER_DEPENDENCY_TSV
py -3 ../audit/verify_output.py ../.audit-local
```

The replay starts with no project `.olean` files, verifies the source manifest, builds the root and its import closure, and runs the paper, full-type and axiom entries. The optional mathlib cache covers external dependencies. The declaration audit traverses both types and bodies. It requires the new flux, the `7/3` energy bound, the `3/14` signed comparison, and the three phase branches in the large-order proof body. It excludes the historical 43-endpoint table, the `25/16` energy route, and the old large-order result. The transitive axiom set is `propext`, `Classical.choice`, and `Quot.sound`.

## Manuscript source

The TeX file is self-contained. From `paper/`, run `xelatex -interaction=nonstopmode -halt-on-error main.tex` until references stabilize. The [paper hashes](paper/SHA256SUMS.txt) identify the current 36-page XeLaTeX build. Its Theorem 1 proof branches at the strict first-endpoint cutoff `d₁ < 3/[100m² log(100m)]`; the complementary branch includes equality and charges the central remainder once. The paper’s AI-use statement is included in the manuscript. The [`single-ramp-v1` tag](https://github.com/Orc-Lee-Chem/springer-lean/tree/single-ramp-v1) retains the earlier publication version; this manuscript revision leaves the Lean sources unchanged.
