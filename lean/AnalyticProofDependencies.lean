import PaperStatementsAudit
import Lean.Util.FoldConsts

open Lean Elab Command

set_option maxHeartbeats 0

private def declarationModule (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some index => (env.allImportedModuleNames[index.toNat]?.getD .anonymous).toString
  | none => ""

private def isProjectDeclaration (env : Environment) (name : Name) : Bool :=
  let source := declarationModule env name
  source.startsWith "SpringerLean" || source == "PaperStatementsAudit"

private def writeProjectDependencies
    (env : Environment) (root : Name) (visited : NameSet)
    (out : IO.FS.Stream) : CommandElabM NameSet := do
  let mut done := visited
  let mut pending := #[root]
  while let some name := pending.back? do
    pending := pending.pop
    if done.contains name then continue
    done := done.insert name
    let some info := env.find? name | throwError "No constant info for {name}"
    let source := declarationModule env name
    out.putStrLn s!"DECL\t{name}\t{source}"
    let typeDeps := info.type.getUsedConstants
    let bodyDeps := match info.value? (allowOpaque := true) with
      | some body => body.getUsedConstants
      | none => #[]
    if let .thmInfo _ := info then
      if bodyDeps.isEmpty then
        throwError "No inspectable proof dependencies for {name}"
    for dep in typeDeps do
      if isProjectDeclaration env dep then
        out.putStrLn s!"TYPE\t{name}\t{dep}"
        pending := pending.push dep
    for dep in bodyDeps do
      if isProjectDeclaration env dep then
        out.putStrLn s!"BODY\t{name}\t{dep}"
        pending := pending.push dep
  return done

run_cmd do
  let some destination ← IO.getEnv "SPRINGER_DEPENDENCY_TSV"
    | throwError "Set SPRINGER_DEPENDENCY_TSV to the output path"
  let out ← IO.FS.Handle.mk destination .write
  let stream := IO.FS.Stream.ofHandle out
  let env := (← getEnv).setExporting false
  let roots := #[
    `SpringerLean.PaperStatementsAudit.theorem_1_1_large_751_singleRamp,
    `SpringerLean.AnalyticRevision.exteriorInverseCoeff_large_catalan_and_eq_iff_slit_singleRamp,
    `SpringerLean.AnalyticRevision.actualHarmonicPhase_energy_le_seven_thirds,
    `SpringerLean.PaperStatementsAudit.theorem_9_1_p2_actual_radial,
    `SpringerLean.PaperStatementsAudit.theorem_9_1_p4_actual_radial,
    `SpringerLean.PaperStatementsAudit.theorem_9_1_p6_actual_radial_strong,
    `SpringerLean.PaperStatementsAudit.theorem_9_1_p8_actual_radial_strong,
    `SpringerLean.PaperStatementsAudit.theorem_9_1_p4_to_p8_actual_radial,
    `SpringerLean.originalPolynomial_derivative_root_power_mean_strict,
    `SpringerLean.connectedPolynomialDerivativeMoments_csSup_and_not_attained,
    `SpringerLean.regularStar_universal_factorConstant_iff_even,
    `SpringerLean.evenRegularStar_factorConstant_actual,
    `SpringerLean.odd_regularStar_factorConstant_counterexample,
    `SpringerLean.PaperStatementsAudit.lemma_9_2_connected_lemniscate_exterior_identity,
    `SpringerLean.PaperStatementsAudit.proposition_9_2_strict_derivative_zero_moment,
    `SpringerLean.PaperStatementsAudit.proposition_9_2_exact_supremum_and_nonattainment,
    `SpringerLean.PaperStatementsAudit.lemma_10_1_actual_radial_probability_is_equilibrium,
    `SpringerLean.PaperStatementsAudit.lemma_10_1_actual_factor_constant_formula,
    `SpringerLean.PaperStatementsAudit.theorem_10_1_even_normalized_exterior,
    `SpringerLean.PaperStatementsAudit.theorem_10_1_even_regular_star,
    `SpringerLean.PaperStatementsAudit.theorem_10_1_regularity_parity,
    `SpringerLean.PaperStatementsAudit.theorem_10_1_odd_regular_star_counterexample
  ]
  let mut seen : NameSet := {}
  for root in roots do
    stream.putStrLn s!"ROOT\t{root}"
    seen ← writeProjectDependencies env root seen stream
  stream.flush
