# Jacobian Challenge

A Lean 4 / Mathlib formalization of Kevin Buzzard's Jacobian challenge: the Jacobian variety of a compact Riemann surface.

## Blueprint

The classical mathematical source-of-truth lives in the Lean blueprint, which annotates each node with `\lean{...}` references to the corresponding Lean declarations.

- 📘 [Blueprint web build](https://tangentstorm.github.io/JacobianChallenge/blueprint/) — has a Plain-English toggle so every node reads cleanly to a non-mathematician.
- 🕸️ [Dependency graph](https://tangentstorm.github.io/JacobianChallenge/blueprint/dep_graph_collapsible.html) — section-collapsed overview, click any box to drill in (this is also the live progress tracker). The flat [full graph](https://tangentstorm.github.io/JacobianChallenge/blueprint/dep_graph_document.html) is also linked from the header.
- 📖 [Jacobian, explained](https://tangentproofs.github.io/jacobian-variety/learn/) — plain-English walkthrough of the eleven challenge theorems and the 71 definitions they use, with an honesty review of what is and is not proved.
- 📄 PDFs: [formal only](https://tangentstorm.github.io/JacobianChallenge/jacobian-informal-proof.pdf) · [with Plain-English companion](https://tangentstorm.github.io/JacobianChallenge/jacobian-informal-proof-with-layman.pdf).

## What the project asks for

The public specification lives in `Jacobian/Challenge.lean` and asks for:

- `genus X` for a compact Riemann surface `X`;
- `Jacobian X` as a compact complex Lie additive group of dimension `genus X`;
- the Abel–Jacobi map `Jacobian.ofCurve`;
- pushforward and pullback maps along holomorphic maps;
- the degree of a holomorphic map of compact Riemann surfaces;
- the identity `pushforward f (pullback f P) = degree f • P`.

Four anti-hack theorems in `Challenge.lean` rule out trivial fake constructions (`genus X := 0`, `Jacobian X := PUnit`, etc.), so the implementation has to build real underlying infrastructure.

## Approach

Analytic period-lattice construction:

```
Jacobian X = H⁰(X, Ω¹)* / H₁(X, ℤ)
```

built bottom-up through reusable layers — complex tori → holomorphic forms → period integration → analytic Jacobian → Abel–Jacobi → trace/degree.

See `ref/plan.md` for the full roadmap, phase breakdown, anti-hack audit, and delegation strategy.

## Build

Pinned to `leanprover/lean4:v4.28.0` and `mathlib v4.28.0`.

```bash
lake build Jacobian.Challenge                    # the public target
lake build Jacobian.Solution                     # the assembled solution skeleton
lake build Jacobian                              # everything (slow)
```

Prefer the narrowest module build after a code change (e.g. `lake build Jacobian.ComplexTorus.QuotientMap`).

## Layout

- `Jacobian/Challenge.lean` — frozen public API; every theorem is a `sorry` to be discharged.
- `Jacobian/Solution.lean` — assembled solution skeleton; bodies delegate to production decls.
- `ref/Inventory.md` — narrative inventory of the pinned Mathlib commit (PRESENT / PARTIAL / ABSENT per prerequisite).
- `Jacobian/<Layer>/*.lean` — production infrastructure modules.
- `tex/` — blueprint LaTeX sources.
- `ref/plan.md`, `ref/PROMPT.md`, `ref/methodology.md` — project plan and operating notes.

## License

MIT — see `LICENSE`.
