"""Check the declaration graph emitted from Lean expressions."""

from collections import defaultdict, deque
from pathlib import Path
import sys


PREFIX = "SpringerLean.AnalyticRevision."
ROOT = "SpringerLean.PaperStatementsAudit.theorem_1_1_large_751_singleRamp"
ENERGY = PREFIX + "actualHarmonicPhase_energy_le_seven_thirds"


def paths(edges, root):
    parents = {root: None}
    queue = deque([root])
    while queue:
        node = queue.popleft()
        for child in sorted(edges[node]):
            if child not in parents:
                parents[child] = node
                queue.append(child)
    return parents


def format_path(parents, node):
    chain = [node]
    while parents[node] is not None:
        node = parents[node]
        chain.append(node)
    return "\n  -> ".join(reversed(chain))


def main(tsv):
    modules = {}
    body = defaultdict(set)
    combined = defaultdict(set)
    for line in tsv.read_text(encoding="utf-8").splitlines():
        tag, name, *fields = line.split("\t")
        if tag == "DECL":
            modules[name], = fields
        elif tag in ("BODY", "TYPE"):
            target, = fields
            combined[name].add(target)
            if tag == "BODY":
                body[name].add(target)

    for root in (ROOT, ENERGY):
        if root not in modules:
            raise SystemExit(f"Missing checked declaration {root}")
        reachable = paths(combined, root)
        missing = reachable.keys() - modules.keys()
        if missing:
            raise SystemExit(f"Uninspected declarations from {root}: {sorted(missing)}")
        forbidden = {
            "SpringerLean.PaperStatementsAudit.theorem_1_1_large_751",
            "SpringerLean.exteriorInverseCoeff_large_catalan_and_eq_iff_slit",
            "SpringerLean.exteriorInverseCoeff_candidate_nonslit_false",
            "SpringerLean.actualHarmonicPhase_energy_le_twentyfive_sixteenths",
            "SpringerLean.exteriorInverseCoeff_exists_signed_phase_bound",
            "SpringerLean.exteriorInverseCoeff_candidate_exists_signed_phase_integral",
            "SpringerLean.actualSignedPhaseDensity",
            "SpringerLean.energyMultiplierEndpointRaw",
        }
        old_modules = ("Round1575EnergyEndpointData", "Round1576EnergyEndpointRealQuadratic",
                       "Round1586EnergyCellEndpointBridge", "Round1633ExplicitEnergyCertificate")
        blocked = sorted(name for name in reachable if name in forbidden
                         or modules[name].split(".")[-1] in old_modules)
        if blocked:
            raise SystemExit(f"Historical route reached: {format_path(reachable, blocked[0])}")
        print(f"{root}: {len(reachable)} reachable project declarations in types and bodies")
        print("Historical multiplier data, 25/16 energy, 8/25 density and large theorem absent.")

    required = (
        ENERGY,
        "SingleRamp.clippedLinearFlux",
        PREFIX + "rampFlux",
        PREFIX + "cutFlux_integral_le",
        PREFIX + "singleRampSignedDensity",
        PREFIX + "exteriorInverseCoeff_exists_singleRamp_signed_bound",
        PREFIX + "actualSignedPhaseIntegral_tiny_first_strict",
        PREFIX + "actualSignedPhaseDensity_aligned_le_twoPower",
        PREFIX + "actualSignedPhaseDensity_trueAxis_lt_lower_power",
        "SingleRamp.trueAxisSign",
        "SpringerLean.refinedAffineSmoothPower_moving_Jensen",
        "SpringerLean.exteriorInverseCoeff_sharp_of_eqOn_slit_all_orders",
    )
    from_root = paths(body, ROOT)
    for target in required:
        if target not in from_root:
            raise SystemExit(f"Missing route in proof bodies for {target}")
        print()
        print(format_path(from_root, target))


if __name__ == "__main__":
    main(Path(sys.argv[1]))
