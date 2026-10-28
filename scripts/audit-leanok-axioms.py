#!/usr/bin/env python3
"""Transitive \\leanok audit: catch blueprint nodes marked proof-complete
(\\leanok) whose Lean declarations actually depend on `sorryAx`.

`blueprint_audit.py` checks whether a \\leanok'd decl's *own body* contains
the literal token `sorry`. That misses TRANSITIVE sorries: a decl whose body
is sorry-free but which calls something that bottoms out in a `sorry`
(e.g. `Jacobian.pushforward_pullback` -> ... -> an open `sorry`
declaration). The blueprint then renders such a node green ("proof formalized")
when it is really blue ("statement stated, proof not yet complete").

This script reuses blueprint_audit's tex/decl extraction, then for every
project-internal decl named in a *proof-level* \\leanok block runs
`#print axioms` (via `lake env lean`) and flags any whose axiom set contains
`sorryAx`. Output: the list of green-but-transitively-sorry nodes.

Usage:
    scripts/audit-leanok-axioms.py            # audit all proof-leanok nodes
    scripts/audit-leanok-axioms.py --json     # machine-readable

Exit status is non-zero if any green-but-sorry node is found.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# Reuse the battle-tested tex parsing + decl indexing from blueprint_audit.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import blueprint_audit as ba  # noqa: E402

ROOT = ba.ROOT


def collect_proof_leanok_decls() -> dict[str, list[dict]]:
    """Return {fully-qualified decl name -> [ {label, file} ... ]} for every
    project-internal decl that sits under a proof-level \\leanok (or a
    definitional env-level \\leanok, which is also a proof claim)."""
    out: dict[str, list[dict]] = {}
    for tex_dir in ba.TEX_DIRS:
        for tex in sorted(tex_dir.glob("*.tex")):
            text = tex.read_text(encoding="utf-8")
            for b in ba.parse_tex_blocks(text):
                # A proof claim is asserted by either a proof-block \leanok,
                # or (for definitional envs with no separate proof) an
                # env-level \leanok.
                proof_claim = (b.get("proof") is not None and b["proof"]["has_leanok"])
                env_proof_claim = (
                    b.get("env") in ba.DEFINITIONAL_ENVS
                    and b.get("proof") is None
                    and b.get("has_stmt_leanok")
                )
                if not (proof_claim or env_proof_claim):
                    continue
                for name in b.get("lean_names", []):
                    if not ba.is_project_name(name):
                        continue
                    out.setdefault(name, []).append(
                        {"label": b.get("label", "?"), "file": tex.name}
                    )
    return out


def print_axioms(names: list[str]) -> dict[str, str]:
    """Run `#print axioms` for each name in one `lake env lean` invocation;
    return {name -> raw axioms line}. Names that fail to elaborate map to ''."""
    # Build a scratch Lean file that imports the whole solution and prints
    # axioms for each decl. One file -> one elaboration pass (fast: reuses
    # the prebuilt oleans).
    lines = ["import Jacobian.Solution"]
    for n in names:
        lines.append(f"#print axioms {n}")
    scratch = ROOT / "Jacobian" / "_LeanokAxiomAudit.lean"
    scratch.write_text("\n".join(lines) + "\n", encoding="utf-8")
    try:
        res = subprocess.run(
            ["lake", "env", "lean", str(scratch.relative_to(ROOT))],
            cwd=ROOT, capture_output=True, text=True,
        )
    finally:
        scratch.unlink(missing_ok=True)
    blob = res.stdout + "\n" + res.stderr
    # Output lines look like:
    #   'Name' depends on axioms: [propext, sorryAx, Classical.choice, ...]
    # or (no axioms): 'Name' does not depend on any axioms
    result: dict[str, str] = {n: "" for n in names}
    for m in re.finditer(r"'([^']+)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)", blob):
        result[m.group(1)] = m.group(2)
    return result


def main(argv: list[str]) -> int:
    want_json = "--json" in argv
    decls = collect_proof_leanok_decls()
    names = sorted(decls)
    if not names:
        print("No project-internal proof-\\leanok decls found.", file=sys.stderr)
        return 0

    axioms = print_axioms(names)
    bad: list[dict] = []
    for n in names:
        ax = axioms.get(n, "")
        if "sorryAx" in ax:
            for site in decls[n]:
                bad.append({"decl": n, "axioms": ax, **site})

    if want_json:
        print(json.dumps(bad, indent=2))
    else:
        print(f"Checked {len(names)} proof-\\leanok decls against #print axioms.")
        if not bad:
            print("  All clean: no \\leanok node transitively depends on sorryAx. ✓")
        else:
            print(f"\n=== GREEN-BUT-SORRY: {len(bad)} \\leanok node(s) depend on sorryAx ===")
            for r in bad:
                print(f"  {r['file']}  label={r['label']}")
                print(f"    {r['decl']}")
                print(f"    {r['axioms']}")
            print("\nThese nodes render green in the dep graph but their proofs are")
            print("not actually complete (transitive sorry). Drop their proof \\leanok")
            print("until the dependency closure is sorryAx-free.")

    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
