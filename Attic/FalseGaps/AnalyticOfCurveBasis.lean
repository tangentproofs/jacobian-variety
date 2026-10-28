/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

/--
The basis-aligned analytic carrier for the Jacobian: the complex
torus quotient of `Fin (analyticGenus ℂ X) → ℂ` by the period lattice.
This is the type that `Jacobian/Solution.lean` ULifts to produce
`Jacobian X`.
-/
abbrev BasisAnalyticJacobian : Type :=
  quotient (Fin (analyticGenus ℂ X) → ℂ) (periodFullComplexLattice X)

/--
The analytic Abel-Jacobi map on the basis-aligned carrier.

Pure assembly: lifts `pathIntegralFunctional` through the period quotient.
-/
noncomputable def analyticOfCurve (P : X) : X → BasisAnalyticJacobian X :=
  fun Q => mk (Fin (analyticGenus ℂ X) → ℂ)
    (periodFullComplexLattice X) (pathIntegralFunctional X P Q)

/--
The Abel-Jacobi map sends the base point to zero.

Pure assembly from `pathIntegralFunctional_self`.
-/
lemma analyticOfCurve_self (P : X) :
    analyticOfCurve X P P = 0 := by
  unfold analyticOfCurve
  rw [pathIntegralFunctional_self]
  rfl

/--
Smoothness of the quotient projection `mk` from the model space
to the complex torus.
-/
theorem quotientMk_contMDiff_spec :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞)
      (ComplexTorus.mk (Fin (analyticGenus ℂ X) → ℂ)
        (periodFullComplexLattice X)) :=
  ComplexTorus.contMDiff_mk (periodFullComplexLattice X)

/-- Smoothness specification for the analytic Abel-Jacobi map. -/
theorem analyticOfCurve_contMDiff_spec (P : X) :
    ContMDiff 𝓘(ℂ)
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞) (analyticOfCurve X P) :=
  (quotientMk_contMDiff_spec X).comp (pathIntegralFunctional_contMDiff_spec X P)

/-- Holomorphicity of the analytic Abel-Jacobi map. -/
lemma analyticOfCurve_contMDiff (P : X) :
    ContMDiff 𝓘(ℂ)
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞) (analyticOfCurve X P) :=
  analyticOfCurve_contMDiff_spec X P

/--
Abel injectivity for positive genus.

Top-down obligation. Bottom-up: Abel's theorem — for `0 < g`, the
analytic Abel-Jacobi map separates points. Requires point-separation
by holomorphic 1-forms.

**Goal.** Show `Function.Injective (analyticOfCurve X P)` where
`analyticOfCurve X P : X → BasisAnalyticJacobian X` sends each
point `Q` to the class
`mk (Fin g → ℂ) (periodFullComplexLattice X) (pathIntegralFunctional X P Q)`
in the period quotient `(Fin g → ℂ) ⧸ basisAlignedPeriodSubgroup X`,
and `g = analyticGenus ℂ X ≥ 1`.

Injectivity of this map is the *point-separation* case of **Abel's
theorem**: if `analyticOfCurve X P Q₁ = analyticOfCurve X P Q₂` then
`Q₁ = Q₂`. Equivalently, the degree-1 Abel-Jacobi map
`Q ↦ [Q − P] ∈ Pic⁰(X)` is injective on points of `X`.

#### Mathlib v4.28.0 lemma survey

| Concept / lemma name | Status in Mathlib v4.28.0 |
|---|---|
| `Abel's theorem` (kernel of Abel-Jacobi = principal divisors) | **DOES NOT EXIST.** No formalisation of Abel's theorem in any form. |
| `Divisor`, `WeilDivisor`, `CartierDivisor` on Riemann surfaces | **DOES NOT EXIST.** No divisor theory for complex curves or compact Riemann surfaces. |
| `PicardGroup`, `Pic⁰(X)`, linear equivalence of divisors | **DOES NOT EXIST.** |
| `RiemannRoch` theorem | **DOES NOT EXIST.** No Riemann-Roch for curves or surfaces. |
| `Principal divisor` / `div(f)` for meromorphic functions on surfaces | **DOES NOT EXIST.** `MeromorphicAt` / `MeromorphicOn` exist for functions `𝕜 → E` on normed fields (not on manifolds). No divisor-of-a-meromorphic-function construction. |
| Riemann theta function for higher-genus surfaces | **DOES NOT EXIST.** Mathlib has `jacobiTheta` / `jacobiTheta₂` (one-variable, modular forms context) but nothing for the multi-variable theta function `Θ : ℂᵍ → ℂ` associated to a period matrix. |
| Holomorphic 1-forms on Riemann surfaces separate points | **DOES NOT EXIST.** |
| `MDifferentiable.exists_eq_const_of_compactSpace` | **EXISTS** (`Mathlib.Geometry.Manifold.Complex`). States that a holomorphic function `f : M → F` on a compact connected complex manifold is constant. This is the key ingredient for the Riemann-Roch approach (see below). |
| `QuotientAddGroup.mk` injectivity ↔ trivial kernel | **EXISTS** (project-internal: `mk_injective_iff_subgroup_eq_bot` in `Jacobian/ComplexTorus/MkInjective.lean`). |
| `MonoidHom.ker_eq_bot_iff` | **EXISTS** (`Mathlib.Algebra.Group.Subgroup.Ker`). `f.ker = ⊥ ↔ Function.Injective f`. |

**Search actually run (confirming absence):**
```
lean_local_search "RiemannRoch"    → [] (empty)
lean_local_search "WeilDivisor"    → [] (empty)
lean_local_search "PicardGroup"    → [] (empty)
lean_local_search "Divisor"        → [] (empty, no algebraic-geometry divisors)
leansearch "Abel's theorem divisor Jacobian variety" → no relevant results
leansearch "Riemann-Roch theorem algebraic curve"    → no relevant results
```

#### Mathematical proof routes

**Route (A): Riemann-Roch.** Suppose `Q₁ ≠ Q₂` but
`analyticOfCurve X P Q₁ = analyticOfCurve X P Q₂`. Then the divisor
`(Q₁) − (Q₂)` is principal, i.e. there exists a meromorphic function
`f : X → ℂ∞` with `div(f) = (Q₁) − (Q₂)`. Such `f` has a single
simple pole at `Q₂` and a single simple zero at `Q₁`, hence `f` gives
a holomorphic map `X → ℂℙ¹` of degree 1, i.e. a biholomorphism
`X ≅ ℂℙ¹`. But `ℂℙ¹` has genus 0, contradicting `g ≥ 1`.

This is the most elementary route, but it requires:
- Meromorphic functions on compact Riemann surfaces (absent from Mathlib);
- The notion of degree of a meromorphic function / holomorphic map;
- The fact that degree-1 holomorphic maps are biholomorphisms;
- That `ℂℙ¹` has genus 0 (`analyticGenus ℂ (ℂℙ¹) = 0`).

**Route (B): Direct 1-form separation.** Unwind the quotient:
`analyticOfCurve X P Q₁ = analyticOfCurve X P Q₂` means
`pathIntegralFunctional X P Q₁ − pathIntegralFunctional X P Q₂ ∈ basisAlignedPeriodSubgroup X`.
Since `pathIntegralFunctional X P Q = (∫_P^Q ω₁, …, ∫_P^Q ωₘ)` in
basis coordinates, this says `(∫_{Q₂}^{Q₁} ωⱼ)ⱼ` is a period vector.
Abel's theorem then asserts that this forces `Q₁ = Q₂` (for `g ≥ 1`).
The essential content is that holomorphic 1-forms separate points
modulo periods, which again reduces to the non-existence of
degree-1 meromorphic functions.

**Route (C): Theta function.** The Riemann theta function approach
shows that the Abel-Jacobi image of the symmetric product
`Sym^{g-1}(X)` is exactly the theta divisor `Θ ⊂ J(X)`. For `g ≥ 1`,
the degree-1 Abel-Jacobi map `X → J(X)` is an embedding because its
fibres are connected components of `Θ ∩ (Θ + c)` for a translate,
which for generic `c` are singletons. This is the most powerful but
also the most infrastructure-heavy route.

#### Project-internal dependency analysis

2. **`analyticOfCurve` is *not* a group homomorphism.** It is a bare
   function `X → BasisAnalyticJacobian X`, not a `MonoidHom` or
   `AddMonoidHom`. So `MonoidHom.ker_eq_bot_iff` does not directly
   apply. Injectivity must be proved directly as
   `∀ Q₁ Q₂, analyticOfCurve X P Q₁ = analyticOfCurve X P Q₂ → Q₁ = Q₂`.

3. **`analyticGenus ℂ X ≥ 1` is a hypothesis but has limited API.**
   `analyticGenus_pos_iff_nontrivial` (in
   `Jacobian/HolomorphicForms/AnalyticGenusPos.lean`) equates
   `0 < analyticGenus ℂ X` with `Nontrivial (HolomorphicOneForm ℂ X)`.
   This gives the existence of a non-zero holomorphic 1-form but not
   point-separation.

4. **No meromorphic function theory in the project.** There is no
   `MeromorphicOn` for manifold-valued functions, no divisor type,
   no degree theory for holomorphic maps between Riemann surfaces.

5. **`BasisAnalyticJacobian X` quotient injectivity.** By
   `mk_injective_iff_subgroup_eq_bot`, the quotient map
   `mk : (Fin g → ℂ) → BasisAnalyticJacobian X` is injective iff
   `basisAlignedPeriodSubgroup X = ⊥`. For `g ≥ 1` this is false
   (the period lattice is non-trivial), so injectivity of
   `analyticOfCurve` does *not* reduce to injectivity of `mk`. The
   key content is that `pathIntegralFunctional X P Q₁` and
   `pathIntegralFunctional X P Q₂` can only differ by a period
   vector when `Q₁ = Q₂`.

#### Recommended resolution path

The most economical resolution is to **declare a new `opaque` property
capturing the Abel-theorem injectivity content** alongside
`pathIntegralFunctional` (or in this file), then wire
`analyticOfCurve_injective` as a one-liner assembly.

**Step 1.** Declare in this file (or in a new
`Jacobian/AbelJacobi/AbelTheoremAux.lean`):
```lean
opaque pathIntegralFunctional_injective_mod_periods
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (P : X) (h : 0 < analyticGenus ℂ X) :
    Function.Injective (analyticOfCurve X P)
```
or, more structurally (separating the mathematical content from the
assembly):
```lean
opaque pathIntegralFunctional_separates_points
    (X : Type) [...] (P : X) (h : 0 < analyticGenus ℂ X)
    (Q₁ Q₂ : X)
    (heq : pathIntegralFunctional X P Q₁ - pathIntegralFunctional X P Q₂
           ∈ basisAlignedPeriodSubgroup X) :
    Q₁ = Q₂
```
The second form is preferable because it isolates the Abel-theorem
content ("period-congruent integrals imply equal points") from the
quotient-assembly layer.

**Step 2.** Wire `analyticOfCurve_injective`:
```lean
lemma analyticOfCurve_injective (P : X) (h : 0 < analyticGenus ℂ X) :
    Function.Injective (analyticOfCurve X P) := by
  intro Q₁ Q₂ heq
  apply pathIntegralFunctional_separates_points X P h Q₁ Q₂
  exact QuotientAddGroup.eq.mp heq
```
This collapses the top-down obligation to the named bottom-up
obligation `pathIntegralFunctional_separates_points`.

**Step 3 (future bottom-up).** Discharge
`pathIntegralFunctional_separates_points` via one of:
- A formalised Riemann-Roch argument (requires extensive new Mathlib
  infrastructure: meromorphic functions on manifolds, divisors, degree
  theory, genus-0 classification);
- A direct 1-form separation argument (requires integration theory on
  manifolds, homotopy invariance of integrals, and the classical
  result that holomorphic 1-forms separate points modulo periods on
  compact Riemann surfaces of positive genus);
- `MDifferentiable.exists_eq_const_of_compactSpace` as the key
  Mathlib ingredient: if a degree-1 meromorphic function existed, it
  would give a non-constant holomorphic function on a compact
  connected manifold, contradicting this lemma. But bridging from
  "period-congruent integrals" to "existence of degree-1 meromorphic
  function" still requires divisor theory not in Mathlib.

#### Dependency graph

#### Anti-hack chain position
-/
lemma analyticOfCurve_injective_with_meromorphicData (P : X) (h : 0 < analyticGenus ℂ X)
    (hanalytic :
      ∀ f : HolomorphicForms.MeromorphicMapToSphere X,
        ∀ Q : X, f.poleDivisor = HolomorphicForms.Divisor.point Q →
          f.PoleModulusData ∧ f.BranchedCoverDataOfPoleDegree) :
    Function.Injective (analyticOfCurve X P) := by
  intro Q₁ Q₂ heq
  apply pathIntegralFunctional_separates_points_with_meromorphicData X P h Q₁ Q₂
  unfold analyticOfCurve at heq
  exact QuotientAddGroup.eq.mp heq
  intro f hf
  exact hanalytic f Q₂ hf

/--
Abel injectivity for positive genus.

The route-data version `analyticOfCurve_injective_with_meromorphicData` is
the honest assembly for callers that can supply explicit meromorphic
promotion data; new code should prefer it.

**Un-bundling (2026-05-29) — honest `sorry` reinstated.** This
declaration's signature is *frozen*: it matches the public-facing
`Jacobian/Solution.lean Jacobian₀.ofCurve_inj` (L106) and ultimately
the public anti-hack `Jacobian/Challenge.lean ofCurve_inj`, neither of
which can gain an `hanalytic` parameter without breaking the frozen
spec. Prior to the un-bundling, this proof was "sorry-free" by
calling the bare `pathIntegralFunctional_separates_points` (which
recursively reached `degree_one_meromorphicMap_implies_analyticGenus_zero`
and from there to `MeromorphicMapToSphere.toPoleModulusData` /
`toBranchedCoverDataOfPoleDegree` — the universal-bridge accessors
removed in commit `aa00f436`). Those bridges bottomed out in
`JacobianChallenge.HolomorphicForms.genusZero_singlePoleMeromorphicAnalyticData_nonempty`
(jc0's "genus-zero #4" deep root), so the apparent absence of a `sorry`
here was an *artifact* of the bridges hiding that dependency.

With the bridges retired and the frozen signature preserved, the
honest answer is to leave this body as an explicit `sorry` until jc0
discharges the genus-zero #4 root. Once that lands, this proof
becomes one-line forward from `analyticOfCurve_injective_with_meromorphicData`
by manufacturing `hanalytic` from the discharged genus-zero #4 — but
that step is jc0's work, not this milestone's.

Honest callers that can supply explicit meromorphic promotion data
should use the sibling `analyticOfCurve_injective_with_meromorphicData`
above (L1909), which is the un-strengthened proof and remains
sorry-free.
-/
lemma analyticOfCurve_injective (P : X) (h : 0 < analyticGenus ℂ X) :
    Function.Injective (analyticOfCurve X P) := by
  sorry
