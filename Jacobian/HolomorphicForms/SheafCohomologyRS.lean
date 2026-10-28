import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Sheaf cohomology on a Riemann surface (project API layer)

Project-side wrappers around Mathlib's topological-sheaf and Ext-based
sheaf-cohomology infrastructure, scoped to abelian sheaves on a
topological space `X`. This file is the leaf bank for
`def:sheaf-cohomology-rs` in
`tex/sections/02-holomorphic-forms-and-genus.tex`.

## What lives here

## What is intentionally NOT here

* (was leaf 3) — see `RSSheafCohomologyGroup` below; reinstated as a
  thin project-facing API alias.
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/--
Abelian sheaves on the topology of `X`: a thin alias over
`TopCat.Sheaf AddCommGrpCat (TopCat.of X)`. Plan leaf 1 (TRIVIAL).
-/
abbrev RSAbSheaf (X : Type*) [TopologicalSpace X] : Type _ :=
  TopCat.Sheaf AddCommGrpCat (TopCat.of X)

/--
Sheaf cohomology of an abelian sheaf on `X`, as the project alias
for Mathlib's Ext-based `CategoryTheory.Sheaf.H`. Plan leaf 2 (SHORT).

The `[HasSheafify]` and `[HasExt]` hypotheses are required by
Mathlib's underlying `Sheaf.H` definition (see
`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`); they are not
automatically derivable for the `Opens.grothendieckTopology X` site on
`AddCommGrpCat` in v4.28.0, so they remain as instance arguments at
this layer and propagate to consumers.
-/
noncomputable abbrev RSSheafCohomology
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) (q : ℕ) : Type 0 :=
  Sheaf.H F q

/--
Project-facing alias for the `AddCommGroup` instance on
`RSSheafCohomology X F q`. Plan leaf 3 (TRIVIAL).

Mathlib already provides this instance directly on `Sheaf.H`; the
alias just exposes it under a project-side name for downstream
consumers that want to depend only on this file.
-/
noncomputable abbrev RSSheafCohomologyGroup
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) (q : ℕ) : AddCommGroup (RSSheafCohomology X F q) :=
  inferInstance

/--
Čech cochain complex of an abelian-group-valued presheaf along an
open cover. Plan leaf 4 (MEDIUM).

Thin alias around Mathlib's `CategoryTheory.cechComplexFunctor`,
specialised to the topological-presheaf source category
`(Opens (TopCat.of X))ᵒᵖ ⥤ AddCommGrpCat`. The instance arguments
required by `cechComplexFunctor`
(`HasFiniteProducts (Opens (TopCat.of X))`,
`Preadditive AddCommGrpCat`,
`HasProducts AddCommGrpCat`) are all derivable in Mathlib v4.28.0:
`Opens` is a `CompleteLattice` (so has all small limits, hence finite
products), and `AddCommGrpCat` is a Grothendieck-abelian preadditive
category with all small limits.

No Čech-derived comparison theorem (i.e. quasi-iso to derived global
sections, or `H^*(Cech) ≃ H^*` under good cover hypotheses) is
provided here — that is downstream work tracked separately.
-/
noncomputable abbrev RSCechComplex
    (X : Type*) [TopologicalSpace X]
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of X))
    (F : TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of X)) :
    CochainComplex AddCommGrpCat.{0} ℕ :=
  (cechComplexFunctor (A := AddCommGrpCat.{0}) U).obj F


abbrev RSLineBundleSheaf (X : Type*) [TopologicalSpace X] : Type _ :=
  RSAbSheaf X


noncomputable abbrev RSLineBundleCohomology
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X) (q : ℕ) : Type 0 :=
  RSSheafCohomology X L q

open scoped Manifold in
/--
The `[Module ℂ (RSSheafCohomology X F q)]` instance arguments are not
auto-derivable from `Sheaf.H`'s `AddCommGroup` alone; consumers
provide them (e.g. via a sheaf-of-ℂ-modules realisation, or a
`letI`-built `Module` instance via Mathlib's
`AddCommGroup.toIntModule` and a `ℂ`-action witness). The class only
asserts the two `FiniteDimensional` properties on top of those data.
-/
class FiniteDimensionalSheafCohomologyRS
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X)
    [Module ℂ (RSSheafCohomology X F 0)]
    [Module ℂ (RSSheafCohomology X F 1)] : Prop where
  /-- `H⁰(X, F)` is a finite-dimensional ℂ-vector space. -/
  finiteDimensional_H0 : FiniteDimensional ℂ (RSSheafCohomology X F 0)
  /-- `H¹(X, F)` is a finite-dimensional ℂ-vector space. -/
  finiteDimensional_H1 : FiniteDimensional ℂ (RSSheafCohomology X F 1)

end JacobianChallenge.HolomorphicForms
