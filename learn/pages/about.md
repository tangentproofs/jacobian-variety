# About this site

**jacobian-variety** ([tangentproofs/jacobian-variety](https://github.com/tangentproofs/jacobian-variety)) is a Lean 4 / Mathlib answer to Kevin Buzzard's *Jacobian challenge*. The challenge file, `Jacobian/Challenge.lean`, states an API for the Jacobian of a compact Riemann surface: the genus, the Jacobian as a compact complex Lie group of dimension equal to the genus, the Abel–Jacobi map, pushforward and pullback along holomorphic maps, the degree of a map, and the identity pushforward ∘ pullback = multiplication by the degree. Every proof in it is `sorry`. `Jacobian/Solution.lean` gives real definitions and proofs under the same names, and the [comparator](https://github.com/leanprover/comparator) checks that the statements match exactly. The [project home](../) has the blueprint, the dependency graph and PDFs.

This site reads the Lean back into plain English. Each node is one Lean declaration with its verbatim Lean, a plain-English reading, faithfulness notes and a short quiz. Tick **I think I understand this** when you do. A node counts as understood once everything its statement mentions is understood too.

The [Lean source](src/index.html) is on the site, highlighted, and every "File.lean lines a–b" reference opens those exact lines.

Start with [the statements](#/start), or read the [review](#/review): an independent audit of whether each statement and definition is the classical one. The [Trust](#/trust) page says what was checked, by what, and what was not.

**Why the definitions matter here.** The challenge's theorems constrain its definitions only loosely. A clever but fake `Jacobian` could satisfy some of them. That is why the challenge adds "anti-hack" theorems (genus 0 iff the surface is a sphere; Abel–Jacobi is injective in positive genus), and why this site explains the *definitions* the theorems mention, not just the theorems.

**Credit.** Challenge: Kevin Buzzard. Lean library: Michal Wallace (tangentstorm) working with AI coding agents (MIT licence). Explanations: drafts written by Claude for Grok Bot, not yet reviewed by a person, and possibly wrong. The Lean is the ground truth.
