#!/usr/bin/env python3
"""Replay this finite structural corollary against pinned cached dependencies.

No upstream source or Lake configuration is modified. Each local module and
AP.Basic is rebuilt in a newly created directory. Mathlib's compiled cache must
already be installed in the supplied formal-conjectures checkout.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


def output(command: list[str], cwd: Path) -> str:
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--formal-conjectures", type=Path, required=True)
    parser.add_argument("--output-parent", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    fc = args.formal_conjectures.resolve()
    pins = json.loads((root / "DEPENDENCIES.json").read_text())
    assert output(["git", "rev-parse", "HEAD"], fc) == pins["formal_conjectures"]["commit"]
    assert (fc / "lean-toolchain").read_text().strip() == pins["lean_toolchain"]
    mathlib = fc / ".lake/packages/mathlib"
    assert output(["git", "rev-parse", "HEAD"], mathlib) == pins["mathlib"]["commit"]
    basic_rel = Path("FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean")
    assert digest(fc / basic_rel) == pins["formal_conjectures"]["ap_basic_sha256"]
    for name, expected in pins["prior_profile_chain"]["files"].items():
        assert digest(root / "prior" / name) == expected, name

    parent = args.output_parent.resolve() if args.output_parent else None
    if parent:
        parent.mkdir(parents=True, exist_ok=True)
    build = Path(tempfile.mkdtemp(prefix="erdos142-replay-", dir=parent))
    (build / basic_rel).parent.mkdir(parents=True)
    shutil.copy2(fc / basic_rel, build / basic_rel)
    for source in (root / "prior").glob("*.lean"):
        shutil.copy2(source, build / source.name)
    for name in ["Equidistribution.lean", "Residues.lean", "SparseDrops.lean"]:
        shutil.copy2(root / name, build / name)

    lean_prefix = Path(output(["lake", "env", "lean", "--print-prefix"], fc))
    lean = lean_prefix / "bin" / "lean"
    lean_path = output(["lake", "env", "printenv", "LEAN_PATH"], fc)
    env = os.environ.copy()
    env["LEAN_PATH"] = str(build) + os.pathsep + lean_path
    modules = [
        str(basic_rel.with_suffix("")),
        "ParitySplit", "UpstreamParity", "Doubling", "PrimePower", "LocalGrowth",
        "BehrendModulus", "RegularScales", "Profile", "Density", "Ordinary",
        "Equidistribution", "Residues", "SparseDrops",
    ]
    report = {
        "status": "running",
        "lean_version": output([str(lean), "--version"], build),
        "pins": pins,
        "modules": [],
    }
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    required_audits = {
        "Equidistribution": {
            "Erdos142Equidistribution.interval_discrepancy",
            "Erdos142Equidistribution.logarithmic_near_extremizer_bound",
            "Erdos142Equidistribution.logarithmic_near_extremizer_density_one",
        },
        "Residues": {"Erdos142Equidistribution.residue_discrepancy"},
        "SparseDrops": {
            "Erdos142SparseDrops.slow_step_count",
            "Erdos142SparseDrops.slow_step_fraction",
            "Erdos142SparseDrops.square_drop",
            "Erdos142SparseDrops.square_recovery",
            "Erdos142SparseDrops.ratios_fail_eventual_closeness",
        },
    }
    for module in modules:
        source = build / (module + ".lean")
        command = [str(lean), "-DwarningAsError=true", "-o", module + ".olean", module + ".lean"]
        result = subprocess.run(command, cwd=build, env=env, text=True, capture_output=True)
        log = result.stdout + result.stderr
        log_path = build / (module.replace("/", "_") + ".log")
        log_path.write_text(log)
        audited = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log, re.S)
        audits = {name: [x.strip() for x in axioms.split(",") if x.strip()] for name, axioms in audited}
        if result.returncode == 0:
            assert required_audits.get(module, set()) <= set(audits), (module, "missing axiom audit")
        for name, axioms in audits.items():
            assert set(axioms) <= allowed, (name, axioms)
        report["modules"].append({
            "module": module,
            "source_sha256": digest(source),
            "exit_code": result.returncode,
            "axiom_audits": audits,
        })
        print(f"{'PASS' if result.returncode == 0 else 'FAIL'} {module}", flush=True)
        if result.returncode:
            print(log, flush=True)
            report["status"] = "failed"
            (build / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
            raise SystemExit(result.returncode)
    report["status"] = "passed"
    (build / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Fresh replay and axiom audits passed. Report: {build / 'verification.json'}")


if __name__ == "__main__":
    main()
