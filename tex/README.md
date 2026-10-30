# Informal proof roadmap

This directory contains a standalone informal proof plan for the Jacobian
Challenge. It is paired with the root-level `blueprint/` directory, which
builds a Lean Blueprint web graph from the same TeX source files.

Main entrypoint:

```text
tex/main.tex
```

The document follows the analytic period-lattice construction

```text
J(X) = H^0(X, Omega^1)^dual / H_1(X, Z)
```

and mirrors the current Lean roadmap where possible. Important theorem blocks
carry `\lean{...}` annotations naming the intended Lean declaration or module.

Suggested checks:

```powershell
cd tex
latexmk -pdf main.tex
```

GitHub Actions builds the same file on pushes and pull requests that touch
`tex/**`. Pull requests upload `tex/main.pdf` as the `jacobian-informal-proof`
artifact. Pushes also publish a small GitHub Pages site with the PDF at:

```text
https://tangentproofs.github.io/jacobian-variety/jacobian-informal-proof.pdf
```

The site publishes the Lean Blueprint dependency graph at `/blueprint/`, built
from `blueprint/src/web.tex`.

Useful Lean Blueprint checks from the repository root:

```powershell
python -m leanblueprint.client pdf
python -m leanblueprint.client web
python -m leanblueprint.client checkdecls
```

On this machine the Python package is installed, but the `leanblueprint.exe`
script is not necessarily on PATH, so the `python -m leanblueprint.client ...`
form is the most reliable invocation. The web build still shells out to
`plastex`, so the Python Scripts directory and a TeX distribution containing
`kpsewhich` must also be on PATH.

If no TeX distribution is installed, a useful text-only check is:

```powershell
rg "\\input|\\include" main.tex sections statements
rg "\\lean\\{" tex
```
