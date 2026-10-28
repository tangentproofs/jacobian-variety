# Retired false gaps (goal (d))

Declarations moved here verbatim from the live tree on branch `independent-repair`. Each
gap below is **false as stated** and was **unreachable** from the public API
(`Jacobian/Solution.lean`) by a declaration-level dependency sweep that includes `private`
and auxiliary (`_proof_n`) declarations. Everything that depended on a retired gap was moved
with it (225 + 2 constants, 18 source files); none of it was reachable.

Counterexamples (from `ref/rkirov-gap-comparison.md` §3, checked against the statements):

| gap | declaration (old file) | why it is false |
|---|---|---|
| 5 | `orientable_letterPair_opposite_orientation` (`Periods/TietzeReduction.lean`) | `Orientable` is `Nonempty Unit`, so carries no information; `g = 1`, `word = [a₀]` with `proj := Quotient.mk` satisfies every hypothesis, yet `a₀ ∈ w` and `a₀⁻¹ ∉ w`. |
| 6 | `orientable_handleSwap_grouping` (`TietzeReduction.lean`) | `TietzeEq w v` never introduces letters and never lengthens; `g = 2`, `w = handleBlock 0 ++ handleBlock 0` satisfies the hypotheses but every admissible `v` contains `a₁`. |
| 8 | `wordQuotient_homeomorph_of_inverseCancel_step` (`TietzeReduction.lean`) | `w = [a₀, a₀⁻¹]`, `v = []`: the quotient of `w` is the sphere `S²`, that of `[]` the closed disk. Needs `v ≠ []`. |
| 9 | `tailRotate_geometric_maps` (`Periods/HandleSwapHomeo.lean`) | `g = 1`, `u = [a₀,b₀]`: the arc-pairing classes `{0,2,4}/{1,3,5}` vs `{0,2,5}/{1,3,4}` are not related by any dihedral symmetry of the hexagon, so no relation-conjugating disk homeomorphism exists. |
| 10 | `cut_along_nonTree_yields_unfoldedDisk` (`Periods/DualGraphCut.lean`) | hypotheses are `PUnit` (`Triangulation`, `DualGraph`, `DualSpanningTree`), so it asserts the whole existence half of surface classification with no input; and without orientability `ℝP²` satisfies them while `SideGen` can only express orientation-reversing pairings. |
| 14 | `h1_basis_periodCoordinate_linearIndependent` (`Periods/PeriodFunctional.lean`) | the Type-0 period pairing is the zero placeholder, so every period coordinate row is `0`; not linearly independent for `g ≥ 1`. (Not in the brief's list; retired under the root-cause rule.) |
| 16 | `deRhamComparisonMap1_zero_period_closed_form_vanishing_provider` (`HolomorphicForms/DeRhamComparisonMap.lean`) | with `exteriorDerivative := 0` and `SmoothDiffForm 1 X` a bare product, it unfolds to `ω.2 = 0 → ω.1 = 0`, i.e. `H⁰(X,Ω¹) = 0`, false for `g ≥ 1`. |
| 17 | `hodgeRemainder_periodPayload_exact` (`HolomorphicForms/HodgeProjection.lean`) | unfolds to `ω.2 = 0` for every `ω`, i.e. `Hom(H₁(X,ℤ), ℂ) = 0`, false for `g ≥ 1`. Jointly 16+17 would force `g = 0` *and* `H₁ = 0` for every surface: they contradict each other. |

Kept in the live tree:

* **gap 7** `handleSwap_index_ordering` — true; **now proved** (sorry-free, axiom-clean) in
  `Jacobian/Periods/TietzeReduction.lean`.
* **gaps 11, 12, 13** (`Periods/Hurewicz.lean`) — true but hard, unreachable; left as
  labelled open sorries.

What a corrected de Rham / Hodge statement (16, 17) would need: a real form type with a real
chartwise `d`, exactness as an equation `ω = dF`, and the classical statement "a closed
1-form with all periods zero is exact" — the public Jacobian no longer needs it (genus is
analytic, the lattice is built from integrals of holomorphic forms directly).
