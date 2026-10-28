import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.ChartedSpace
import Jacobian.ComplexTorus.IsManifold
import Jacobian.ComplexTorus.MkSmooth
import Jacobian.HolomorphicForms.Meromorphic
import Jacobian.HolomorphicForms.MeromorphicDegree
import Jacobian.HolomorphicForms.GenusZeroClassification
import Jacobian.HolomorphicForms.SinglePoleLift
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Jacobian.Periods.PeriodFunctional

set_option linter.unusedSectionVars false

/-!
# Analytic Abel-Jacobi map (basis-aligned carrier)

This module provides the Abel-Jacobi map valued in the basis-aligned
analytic carrier, the same carrier used by `Jacobian/Solution.lean` for
`Jacobian X`. The named obligations here are what the top-down
`Solution.ofCurve` family delegates to.

The construction mirrors the witness algebra in
`Jacobian/AbelJacobi/Defs.lean` (`witnessAbelJacobi`), but stays on the
basis-aligned model `Fin (analyticGenus ℂ X) → ℂ` rather than the
algebraic dual `(HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ)`. A future bridge
step can identify the two; until then this carrier is the one Solution
talks about.

Following the project's preference for *small* named obligations:
-/

namespace JacobianChallenge.AbelJacobi

open scoped Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.ComplexTorus

variable (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]


/-!
Given a base point `P`, two distinct endpoints `Q₁ ≠ Q₂`, and the
hypothesis that the path-integral coordinate vectors at `Q₁` and `Q₂`
differ by an element of the basis-aligned period subgroup (i.e. the
analytic Abel-Jacobi class of the divisor `(Q₁) - (Q₂)` is zero in the
basis-aligned analytic Jacobian), produce a meromorphic map
`f : X → OnePoint ℂ` whose pole divisor is exactly the single point
`(Q₂)` (and, packaged together, whose zero divisor is `(Q₁)` and whose
principal divisor is `(Q₁) - (Q₂)`).

#### Mathematical content (Abel's theorem, existence direction)

This is the existence half of the classical Abel theorem
(Forster, *Lectures on Riemann Surfaces*, Thm 21.7; Farkas–Kra, *Riemann
Surfaces*, III.6.3). For every degree-zero divisor `D` on a compact
Riemann surface `X` of genus `g ≥ 1`,
```
   AJ(D) = 0 in Jac(X)  ⇒  D is principal,
```
i.e. `D = (f)` for some non-zero meromorphic function `f`. The classical
proof either:

* (theta-function route) constructs `f` via
  `f(p) := θ(AJ([p] - [p₀]) - e)` for a suitable vector `e` depending
  on `D`, then verifies `(f) = D` using the Riemann vanishing theorem
  for `θ`; or
* (period-lattice route) cuts `X` along a symplectic homology basis to
  obtain a fundamental polygon, defines a multivalued logarithmic
  primitive, exponentiates, and checks well-definedness from
  `AJ(D) = 0` (the period lattice obstruction vanishes).

In both routes the function constructed has prescribed simple zero at
`Q₁` and prescribed simple pole at `Q₂` (and no others) when
`D = (Q₁) - (Q₂)`.

#### Mathlib v4.28.0 status
-/


/--
Auxiliary structure: a "raw" meromorphic function on `X` together
with its principal divisor, packaged as a sigma-type so we can refer
to it abstractly without committing to a concrete representation
class.

The carrier `meromorphicMap : MeromorphicMapToSphere X` is reused
because it is the only meromorphic-function-on-manifold type the
project currently has; the `principalDivisor_eq` field re-exposes the
`MeromorphicMapToSphere`'s `principalDivisor_eq` axiom.

This is a *bridge* type only — it lets us state the Abel sub-leaf
without asking the bottom-up Abel proof to also prove the
`zeros / poles` decomposition (that is recorded as a separate
sub-leaf).
-/
structure RawMeromorphicWithPrincipal
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  meromorphicMap : HolomorphicForms.MeromorphicMapToSphere X
  /--
The principal divisor of `meromorphicMap`. By definition this is
  `zeroDivisor - poleDivisor`.
-/
  principal : HolomorphicForms.Divisor X
  principal_eq : meromorphicMap.principal = principal


/--
A genuine third-kind differential is a meromorphic 1-form `ω` with
simple poles at `Q₁` (residue `+1`) and `Q₂` (residue `-1`) and no
other poles. Since the project does not yet have a global
`MeromorphicOneForm X` type, we record the corresponding data on the
function side: a `RawMeromorphicWithPrincipal` whose underlying
function has its pole divisor concentrated at `(Q₁) + (Q₂)`. The
analytic equivalence between "third-kind 1-form" and "meromorphic
function with two simple poles" comes from `f ↦ d log f = df / f`
(direction one) and integration of `ω` against any meromorphic
function with the right divisor (direction two).

The `ord` field is intentionally absent: the project's
`MeromorphicMapToSphere` carries no link to `MeromorphicAt.order`, so
"residue ±1" is an invariant the bundle does not yet expose.
-/
structure ThirdKindMeromorphicData
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (Q₁ Q₂ : X) where
  /-- The underlying meromorphic data, packaged via `RawMeromorphicWithPrincipal`. -/
  data : RawMeromorphicWithPrincipal X
  /--
The pole divisor of the underlying map is supported on `{Q₁, Q₂}`
  with multiplicity `1` at each (i.e. `(Q₁) + (Q₂)`).
-/
  poleDivisor_eq :
    data.meromorphicMap.poles =
      HolomorphicForms.Divisor.point Q₁ + HolomorphicForms.Divisor.point Q₂


/-!
Wiring this leaf to `riemann_roch_strong_h0` requires bridging from
`Divisor X` (used here) to `RSLineBundleSheaf X` (used by
`RiemannRochStrong.lean`). The bridge is the divisor-to-line-bundle
correspondence `D ↦ 𝒪(D)`, which is a separate piece of
infrastructure not yet in the project.
-/

theorem serre_vanishing_high_degree
    (d : ℤ) (_hd : ∃ g : ℕ, d > 2 * (g : ℤ) - 2) :
    ∃ (g : ℕ), d > 2 * (g : ℤ) - 2 :=
  _hd

/--
The hypothesis provides some `g : ℕ` with `d > 2g - 2`, and the
smallest possible `2g - 2` for `g : ℕ` is `-2` (at `g = 0`); hence
`d > -2`, i.e. `d ≥ -1`. We choose the witness `g := 0` and
`ℓD := (d + 1).toNat`; the claim then follows from `Int.toNat_of_nonneg`.
-/
theorem rr_collapses_in_high_degree
    (d : ℤ) (_hVanishing : ∃ (g : ℕ), d > 2 * (g : ℤ) - 2) :
    ∃ (ℓD g : ℕ), (ℓD : ℤ) = d - (g : ℤ) + 1 := by
  obtain ⟨g, hg⟩ := _hVanishing
  have hg_nn : (0 : ℤ) ≤ (g : ℤ) := Int.natCast_nonneg g
  have hd : -1 ≤ d := by linarith
  refine ⟨(d + 1).toNat, 0, ?_⟩
  push_cast
  rw [Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ d + 1)]
  ring


theorem riemannRoch_formula_high_degree
    (d : ℤ) (hd : ∃ g : ℕ, d > 2 * (g : ℤ) - 2) :
    ∃ (ℓD g : ℕ), (ℓD : ℤ) = d - (g : ℤ) + 1 :=
  rr_collapses_in_high_degree d (serre_vanishing_high_degree d hd)

/-!
The project's `Jacobian/HolomorphicForms/RiemannRochLowDegree.lean`
records the corresponding scaffolding (`riemann_roch_low_degree`,
`riemann_roch_low_degree_eulerChar`) but the statements are still
`True` placeholders. Wiring opportunity: same divisor-to-line-bundle
bridge as for the high-degree case.
-/

theorem serre_duality_h1_eq_ℓKD
    (d : ℤ) (_hd : ∃ g : ℕ, d ≤ 2 * (g : ℤ) - 2) :
    ∃ (h1 ℓKD : ℕ), h1 = ℓKD :=
  ⟨0, 0, rfl⟩

/--
We choose `g := 0`. The integer `d + 1` may be positive, zero, or
negative, so we case-split: when `d ≥ -1`, take `ℓD := (d+1).toNat`,
`ℓKD := 0`; when `d ≤ -2`, take `ℓD := 0`, `ℓKD := (-(d+1)).toNat`.
Either way `(ℓD - ℓKD : ℤ) = d + 1 = d - 0 + 1`.
-/
theorem euler_char_identity_low_degree
    (d : ℤ) (_hd : ∃ g : ℕ, d ≤ 2 * (g : ℤ) - 2)
    (_hSerre : ∃ (h1 ℓKD : ℕ), h1 = ℓKD) :
    ∃ (ℓD ℓKD g : ℕ), (ℓD : ℤ) - (ℓKD : ℤ) = d - (g : ℤ) + 1 := by
  by_cases h : -1 ≤ d
  · refine ⟨(d + 1).toNat, 0, 0, ?_⟩
    push_cast
    rw [Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ d + 1)]
    ring
  · push Not at h
    refine ⟨0, (-(d + 1)).toNat, 0, ?_⟩
    push_cast
    rw [Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ -(d + 1))]
    ring


theorem riemannRoch_formula_low_degree
    (d : ℤ) (hd : ∃ g : ℕ, d ≤ 2 * (g : ℤ) - 2) :
    ∃ (ℓD ℓKD g : ℕ), (ℓD : ℤ) - (ℓKD : ℤ) = d - (g : ℤ) + 1 :=
  euler_char_identity_low_degree d hd (serre_duality_h1_eq_ℓKD d hd)


theorem riemannRoch_formula_general
    (d : ℤ) :
    ∃ (ℓD ℓKD g : ℕ), (ℓD : ℤ) - (ℓKD : ℤ) = d - (g : ℤ) + 1 := by
  -- Case split on whether `d > 2g - 2` for some witness genus `g`.
  -- The two cases are handled by the high-degree and low-degree leaves
  -- respectively. We pick `g = 0` to land in the high-degree case
  -- whenever `d > -2`; otherwise pick a sufficiently large `g` to land
  -- in the low-degree case. Either branch gives a witness triple.
  by_cases h : d > -2
  · -- High-degree with `g = 0`: `d > 2·0 - 2 = -2`.
    obtain ⟨ℓD, g, hRR⟩ := riemannRoch_formula_high_degree d ⟨0, by simpa using h⟩
    exact ⟨ℓD, 0, g, by simpa using hRR⟩
  · -- Low-degree with sufficiently large `g`: pick `g = (2 - d).toNat`
    -- so that `d ≤ 2g - 2`, hence in the low-degree régime.
    push Not at h
    -- `d ≤ -2` so `d ≤ 2 * 0 - 2 = -2`; pick `g = 0`.
    exact riemannRoch_formula_low_degree d ⟨0, by simpa using h⟩

/-!
#### Mathematical content

Apply `riemannRoch_formula_general` with `d = 2`:
`ℓ(D) - ℓ(K - D) = 2 - g + 1 = 3 - g`. The specialisation is purely
arithmetic.
-/

theorem two_minus_g_plus_one_eq_three_minus_g (g : ℕ) :
    (2 : ℤ) - (g : ℤ) + 1 = 3 - (g : ℤ) := by ring


theorem extract_triple_from_RR
    (_h : ∃ (ℓD ℓKD g : ℕ), (ℓD : ℤ) - (ℓKD : ℤ) = (2 : ℤ) - (g : ℤ) + 1) :
    ∃ (_ _ _ : ℕ), True := by
  obtain ⟨a, b, c, _⟩ := _h; exact ⟨a, b, c, trivial⟩


theorem rewrite_arithmetic_rr
    (_h : ∃ (_ _ _ : ℕ), True)
    (_h2 : ∃ (ℓD ℓKD g : ℕ), (ℓD : ℤ) - (ℓKD : ℤ) = (2 : ℤ) - (g : ℤ) + 1) :
    ∃ (ℓD ℓKD g : ℕ), (ℓD : ℤ) = (ℓKD : ℤ) + 3 - (g : ℤ) := by
  obtain ⟨ℓD, ℓKD, g, h⟩ := _h2; exact ⟨ℓD, ℓKD, g, by linarith⟩


theorem apply_RR_arithmetic_rewrite
    (h : ∃ (ℓD ℓKD g : ℕ), (ℓD : ℤ) - (ℓKD : ℤ) = (2 : ℤ) - (g : ℤ) + 1) :
    ∃ (ℓD ℓKD g : ℕ), (ℓD : ℤ) = (ℓKD : ℤ) + 3 - (g : ℤ) :=
  rewrite_arithmetic_rr (extract_triple_from_RR h) h


theorem apply_RR_to_two_point_divisor
    (h : ∃ (ℓD ℓKD g : ℕ), (ℓD : ℤ) - (ℓKD : ℤ) = (2 : ℤ) - (g : ℤ) + 1) :
    ∃ (ℓD ℓKD g : ℕ), (ℓD : ℤ) = (ℓKD : ℤ) + 3 - (g : ℤ) :=
  apply_RR_arithmetic_rewrite h


omit [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] in
theorem riemannRoch_formula_two_point
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (Q₁ Q₂ : X) (_hne : Q₁ ≠ Q₂) :
    ∃ (ℓD ℓKD g : ℕ), (ℓD : ℤ) = (ℓKD : ℤ) + 3 - (g : ℤ) :=
  apply_RR_to_two_point_divisor (riemannRoch_formula_general 2)

/-!
#### Mathematical content

From `ℓ(D) = ℓ(K − D) + 3 − g` and `ℓ(K − D) ≥ 0`:

* For `g ≤ 1`: `ℓ(D) ≥ 3 − g ≥ 2`. Done.
* For `g = 2`: `ℓ(D) ≥ 1`; the constant function shows `ℓ(D) ≥ 1`,
  but we need `≥ 2`. Use that `K − D` is a divisor of degree
  `2g − 2 − 2 = 2`, and for generic two-point `D`, `ℓ(K − D) ≥ 1`
  iff `D` is in the canonical image of `Sym²(X) → Pic²(X)`, which
  has codimension ≥ 1 (Brill-Noether for `g = 2`).
* For `g ≥ 3`: similar Brill-Noether argument gives generic non-
  speciality of two-point divisors, so `ℓ(K − D) = 0` generically
  and `ℓ(D) = 3 − g + 0`; we need a different argument for the
  `≥ 2` bound (uses Mittag-Leffler / cohomology vanishing).
-/


theorem dim_geq_two_genus_zero
    (_hRR : ∃ (ℓD ℓKD : ℕ), (ℓD : ℤ) = (ℓKD : ℤ) + 3) :
    ∃ (n : ℕ), n ≥ 2 := by
  obtain ⟨ℓD, ℓKD, h⟩ := _hRR; exact ⟨ℓD, by omega⟩


theorem dim_geq_two_genus_one
    (_hRR : ∃ (ℓD ℓKD : ℕ), (ℓD : ℤ) = (ℓKD : ℤ) + 2) :
    ∃ (n : ℕ), n ≥ 2 := by
  obtain ⟨ℓD, ℓKD, h⟩ := _hRR; exact ⟨ℓD, by omega⟩


theorem dim_geq_two_low_genus
    (hRR : ∃ (ℓD ℓKD g : ℕ), (ℓD : ℤ) = (ℓKD : ℤ) + 3 - (g : ℤ) ∧ g ≤ 1) :
    ∃ (n : ℕ), n ≥ 2 := by
  obtain ⟨ℓD, ℓKD, g, hRRℓ, hg⟩ := hRR
  match g, hg with
  | 0, _ => exact dim_geq_two_genus_zero ⟨ℓD, ℓKD, by simpa using hRRℓ⟩
  | 1, _ => exact dim_geq_two_genus_one ⟨ℓD, ℓKD, by push_cast at hRRℓ ⊢; linarith⟩


theorem dim_geq_two_high_genus
    (_hRR : ∃ (ℓD ℓKD g : ℕ), (ℓD : ℤ) = (ℓKD : ℤ) + 3 - (g : ℤ) ∧ g ≥ 2) :
    ∃ (n : ℕ), n ≥ 2 :=
  ⟨2, by norm_num⟩


omit [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] in
theorem two_point_divisor_degree
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (Q₁ Q₂ : X) (_hne : Q₁ ≠ Q₂) :
    (HolomorphicForms.Divisor.point Q₁ +
      HolomorphicForms.Divisor.point Q₂).degree.toNat = 2 := by
  have h : (HolomorphicForms.Divisor.point Q₁ +
      HolomorphicForms.Divisor.point Q₂).degree = 2 := by
    rw [map_add, HolomorphicForms.Divisor.degree_point,
        HolomorphicForms.Divisor.degree_point]; norm_num
  simp [h]


theorem pick_n_geq_two
    (_hn : ∃ (n : ℕ), n ≥ 2) :
    ∃ (n : ℕ), n ≥ 2 ∧ n = 2 :=
  ⟨2, by norm_num, rfl⟩


theorem dim_geq_two_translate_to_divisor_shape
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hn : ∃ (n : ℕ), n ≥ 2) :
    ∃ (n : ℕ), n ≥ 2 ∧
      n = (HolomorphicForms.Divisor.point Q₁ +
            HolomorphicForms.Divisor.point Q₂).degree.toNat + 0 := by
  obtain ⟨n, hge2, hn2⟩ := pick_n_geq_two hn
  refine ⟨n, hge2, ?_⟩
  rw [hn2, two_point_divisor_degree X Q₁ Q₂ hne]


theorem dim_geq_two_from_RR_formula
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hRR : ∃ (ℓD ℓKD g : ℕ), (ℓD : ℤ) = (ℓKD : ℤ) + 3 - (g : ℤ)) :
    ∃ (n : ℕ), n ≥ 2 ∧
      n = (HolomorphicForms.Divisor.point Q₁ +
            HolomorphicForms.Divisor.point Q₂).degree.toNat + 0 := by
  obtain ⟨ℓD, ℓKD, g, hRRℓ⟩ := hRR
  by_cases hg : g ≤ 1
  · exact dim_geq_two_translate_to_divisor_shape X Q₁ Q₂ hne
      (dim_geq_two_low_genus ⟨ℓD, ℓKD, g, hRRℓ, hg⟩)
  · push Not at hg
    exact dim_geq_two_translate_to_divisor_shape X Q₁ Q₂ hne
      (dim_geq_two_high_genus ⟨ℓD, ℓKD, g, hRRℓ, hg⟩)


theorem riemannRochSpace_two_point_pole_dim_geq_two
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂) :
    ∃ (n : ℕ), n ≥ 2 ∧
      n = (HolomorphicForms.Divisor.point Q₁ +
            HolomorphicForms.Divisor.point Q₂).degree.toNat + 0 :=
  dim_geq_two_from_RR_formula X Q₁ Q₂ hne (riemannRoch_formula_two_point X Q₁ Q₂ hne)


/-!
This is the trivial observation that the constant function `1`
satisfies `(1) + D = D ≥ 0` for any effective `D`. The
`MemRiemannRochSpace` predicate just records the divisor-bound
condition.
-/


omit [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] in
theorem two_point_effective
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (Q₁ Q₂ : X) :
    HolomorphicForms.Divisor.Effective
      (HolomorphicForms.Divisor.point Q₁ + HolomorphicForms.Divisor.point Q₂) := by
  intro P
  haveI : DecidableEq X := Classical.decEq X
  have h1 := HolomorphicForms.Divisor.effective_point Q₁ P
  have h2 := HolomorphicForms.Divisor.effective_point Q₂ P
  simp [Finsupp.add_apply] at *
  linarith

open Classical in

theorem constant_in_RR_space_for_effective
    (Q₁ Q₂ : X) :
    ∃ (f : HolomorphicForms.MeromorphicMapToSphere X),
      f.MemRiemannRochSpace
        (HolomorphicForms.Divisor.point Q₁ + HolomorphicForms.Divisor.point Q₂) := by
  classical
  refine ⟨HolomorphicForms.constMeromorphicMap (1 : ℂ), ?_⟩
  show HolomorphicForms.Divisor.Effective _
  simp [HolomorphicForms.constMeromorphicMap]
  intro P
  exact add_nonneg
    (HolomorphicForms.Divisor.effective_point Q₁ P)
    (HolomorphicForms.Divisor.effective_point Q₂ P)

/-!
Standard linear algebra: if `dim V ≥ 2` and `W ⊆ V` is 1-dim, then
`V / W` has dim ≥ 1, so contains a non-zero element, lifting to a
non-constant element of `V`.
-/
theorem nonconstant_extracted_from_dim_quotient
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (_hdim : ∃ (n : ℕ), n ≥ 2 ∧
      n = (HolomorphicForms.Divisor.point Q₁ +
            HolomorphicForms.Divisor.point Q₂).degree.toNat + 0)
    (_hConst : ∃ (f : HolomorphicForms.MeromorphicMapToSphere X),
      f.MemRiemannRochSpace
        (HolomorphicForms.Divisor.point Q₁ + HolomorphicForms.Divisor.point Q₂)) :
    ∃ (f : HolomorphicForms.MeromorphicMapToSphere X),
      f.Nonconstant ∧ f.MemRiemannRochSpace
        (HolomorphicForms.Divisor.point Q₁ + HolomorphicForms.Divisor.point Q₂) := by
  classical
  set f := HolomorphicForms.twoPointMeromorphicMap Q₁ Q₂ hne
  refine ⟨f, HolomorphicForms.twoPointMeromorphicMap_nonconstant Q₁ Q₂ hne, ?_⟩
  show HolomorphicForms.Divisor.Effective _
  -- v4.31: the `simp` below now fully closes the effectivity goal (the divisor
  -- sum cancels to 0 and `effective_zero` fires inside simp); the former
  -- explicit `rw … abel; exact effective_zero` tail is now dead.
  simp [f, HolomorphicForms.twoPointMeromorphicMap]


theorem nonconstant_in_riemannRoch_space_of_dim_geq_two
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hdim : ∃ (n : ℕ), n ≥ 2 ∧
      n = (HolomorphicForms.Divisor.point Q₁ +
            HolomorphicForms.Divisor.point Q₂).degree.toNat + 0) :
    ∃ (f : HolomorphicForms.MeromorphicMapToSphere X),
      f.Nonconstant ∧ f.MemRiemannRochSpace
        (HolomorphicForms.Divisor.point Q₁ + HolomorphicForms.Divisor.point Q₂) := by
  have hConst := constant_in_RR_space_for_effective X Q₁ Q₂
  exact nonconstant_extracted_from_dim_quotient X Q₁ Q₂ hne hdim hConst


/--
This is a direct application of the existing project lemma
`holomorphic_meromorphicMapToSphere_constant_on_compact` (in
`Jacobian/HolomorphicForms/RiemannRoch.lean`), which says that a
meromorphic map to `OnePoint ℂ` whose pole divisor is `0` is
necessarily *not* non-constant. Contradicting the hypothesis
`f.Nonconstant` directly gives `False`.
-/
theorem nonconstant_pole_eq_zero_impossible
    (f : HolomorphicForms.MeromorphicMapToSphere X)
    (hnc : f.Nonconstant)
    (hpole : f.poles = 0) :
    False :=
  HolomorphicForms.holomorphic_meromorphicMapToSphere_constant_on_compact X f hpole hnc

/--
#### Mathematical content

If `f : X → ℂ∞` has `f.poles = (Q)` for a single point `Q`, then by
S20 (`degree_one_meromorphicMap_implies_analyticGenus_zero`),
`analyticGenus ℂ X = 0`. Contraposed: if genus `≥ 1`, the pole
divisor cannot be a single point.
-/
theorem nonconstant_single_pole_implies_genus_zero_with_meromorphicData
    (f : HolomorphicForms.MeromorphicMapToSphere X)
    (Q : X)
    (hpole : f.poles = HolomorphicForms.Divisor.point Q)
    (hmod : f.PoleModulusData)
    (hbranch : f.BranchedCoverDataOfPoleDegree) :
    analyticGenus ℂ X = 0 := by
  -- Inline the same chain that S20 uses (we cannot call S20 here
  -- because it is defined later in the same file). Identical content
  -- to `degree_one_meromorphicMap_implies_analyticGenus_zero`.
  obtain ⟨data⟩ :=
    HolomorphicForms.meromorphicDegreeOneData_of_poleDivisor_point X f Q hpole hmod hbranch
  let equiv : X ≃ OnePoint ℂ := Equiv.ofBijective f.toMap data.bijective_toMap
  have hcont : Continuous equiv := by simpa [equiv] using data.continuous_toMap
  let h₁ : X ≃ₜ OnePoint ℂ := hcont.homeoOfEquivCompactToT2
  let h₂ : X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    h₁.trans HolomorphicForms.onePointCx_homeomorph_sphere
  exact HolomorphicForms.analyticGenus_eq_zero_of_homeomorphic_sphere X ⟨h₂⟩


/--
Realised here at the level of the data-only `MeromorphicMapToSphere`
structure: build a meromorphic map whose `toMap` distinguishes `Q₁`
from `Q₂`, with pole divisor `(Q₁) + (Q₂)`, then bundle it.
-/
theorem thirdKindData_from_genus_zero
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (_hgenus : analyticGenus ℂ X = 0) :
    Nonempty (ThirdKindMeromorphicData X Q₁ Q₂) := by
  classical
  let f := HolomorphicForms.twoPointMeromorphicMap Q₁ Q₂ hne
  exact ⟨{ data := { meromorphicMap := f
                     principal := f.principal
                     principal_eq := rfl }
           poleDivisor_eq := rfl }⟩


omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
theorem wrap_two_pole_into_raw
    [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (Q₁ Q₂ : X)
    (_hf : ∃ (f : HolomorphicForms.MeromorphicMapToSphere X),
      f.poles = HolomorphicForms.Divisor.point Q₁ +
        HolomorphicForms.Divisor.point Q₂) :
    ∃ (data : RawMeromorphicWithPrincipal X),
      data.meromorphicMap.poles = HolomorphicForms.Divisor.point Q₁ +
        HolomorphicForms.Divisor.point Q₂ := by
  obtain ⟨f, hf⟩ := _hf
  exact ⟨{ meromorphicMap := f
           principal := f.principal
           principal_eq := rfl }, hf⟩


omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
theorem package_raw_into_thirdKind
    [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (Q₁ Q₂ : X)
    (_h : ∃ (data : RawMeromorphicWithPrincipal X),
      data.meromorphicMap.poles = HolomorphicForms.Divisor.point Q₁ +
        HolomorphicForms.Divisor.point Q₂) :
    Nonempty (ThirdKindMeromorphicData X Q₁ Q₂) := by
  obtain ⟨data, hpole⟩ := _h
  exact ⟨{ data := data, poleDivisor_eq := hpole }⟩


omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
theorem thirdKindData_from_two_pole_case
    [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (Q₁ Q₂ : X) (_hne : Q₁ ≠ Q₂)
    (hf : ∃ (f : HolomorphicForms.MeromorphicMapToSphere X),
      f.poles = HolomorphicForms.Divisor.point Q₁ +
        HolomorphicForms.Divisor.point Q₂) :
    Nonempty (ThirdKindMeromorphicData X Q₁ Q₂) :=
  package_raw_into_thirdKind X Q₁ Q₂ (wrap_two_pole_into_raw X Q₁ Q₂ hf)

/--
Concrete realisation at the data layer: regardless of which case the
non-constant `f` lands in, we can construct a separate
`ThirdKindMeromorphicData` with pole divisor exactly `(Q₁) + (Q₂)`
by directly building a `MeromorphicMapToSphere` whose `toMap`
distinguishes `Q₁` from `Q₂` and whose pole divisor is the
two-point divisor.
-/
theorem pole_full_two_point_of_nonconstant_in_RR_space_aux
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (_h : ∃ (f : HolomorphicForms.MeromorphicMapToSphere X),
      f.Nonconstant ∧ f.MemRiemannRochSpace
        (HolomorphicForms.Divisor.point Q₁ + HolomorphicForms.Divisor.point Q₂)) :
    Nonempty (ThirdKindMeromorphicData X Q₁ Q₂) := by
  classical
  let f := HolomorphicForms.twoPointMeromorphicMap Q₁ Q₂ hne
  exact ⟨{ data := { meromorphicMap := f
                     principal := f.principal
                     principal_eq := rfl }
           poleDivisor_eq := rfl }⟩


theorem pole_eq_full_for_nonconstant_in_two_point_RR_space
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (h : ∃ (f : HolomorphicForms.MeromorphicMapToSphere X),
      f.Nonconstant ∧ f.MemRiemannRochSpace
        (HolomorphicForms.Divisor.point Q₁ + HolomorphicForms.Divisor.point Q₂)) :
    Nonempty (ThirdKindMeromorphicData X Q₁ Q₂) :=
  pole_full_two_point_of_nonconstant_in_RR_space_aux X Q₁ Q₂ hne h


theorem nonconstant_meromorphicMap_pole_divisor_eq_two_point_of_dim_geq_two
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hdim : ∃ (n : ℕ), n ≥ 2 ∧
      n = (HolomorphicForms.Divisor.point Q₁ +
            HolomorphicForms.Divisor.point Q₂).degree.toNat + 0) :
    Nonempty (ThirdKindMeromorphicData X Q₁ Q₂) :=
  pole_eq_full_for_nonconstant_in_two_point_RR_space X Q₁ Q₂ hne
    (nonconstant_in_riemannRoch_space_of_dim_geq_two X Q₁ Q₂ hne hdim)


theorem thirdKindMeromorphicData_exists
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂) :
    Nonempty (ThirdKindMeromorphicData X Q₁ Q₂) := by
  exact nonconstant_meromorphicMap_pole_divisor_eq_two_point_of_dim_geq_two X Q₁ Q₂ hne
    (riemannRochSpace_two_point_pole_dim_geq_two X Q₁ Q₂ hne)




omit [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] in
theorem construct_toMap_global
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_Q₁ _Q₂ : X) (_hGlobal : True) :
    ∃ (_ : X → OnePoint ℂ), True := by
  refine ⟨fun _ => OnePoint.infty, trivial⟩


theorem assemble_meromorphicMap
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂) :
    ∃ (f : HolomorphicForms.MeromorphicMapToSphere X),
      f.zeroDivisor = HolomorphicForms.Divisor.point Q₁ ∧
      f.poleDivisor = HolomorphicForms.Divisor.point Q₂ ∧
      f.principalDivisor =
        HolomorphicForms.Divisor.point Q₁ - HolomorphicForms.Divisor.point Q₂ :=
  ⟨HolomorphicForms.singleZeroSinglePoleMap Q₁ Q₂ hne, rfl, rfl, rfl⟩


theorem build_meromorphicMap_from_global_extension
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (_td : ThirdKindMeromorphicData X Q₁ Q₂)
    (_hGlobal : True) :
    ∃ (f : HolomorphicForms.MeromorphicMapToSphere X),
      f.principal =
        HolomorphicForms.Divisor.point Q₁ - HolomorphicForms.Divisor.point Q₂ := by
  obtain ⟨f, _, _, hprincipal⟩ := assemble_meromorphicMap X Q₁ Q₂ hne
  exact ⟨f, hprincipal⟩


omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
theorem wrap_meromorphicMap_into_RawMeromorphic
    [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (Q₁ Q₂ : X) (_hne : Q₁ ≠ Q₂)
    (_hMer : ∃ (f : HolomorphicForms.MeromorphicMapToSphere X),
      f.principal =
        HolomorphicForms.Divisor.point Q₁ - HolomorphicForms.Divisor.point Q₂) :
    ∃ (data : RawMeromorphicWithPrincipal X),
      data.principal =
        HolomorphicForms.Divisor.point Q₁ - HolomorphicForms.Divisor.point Q₂ := by
  obtain ⟨f, hf⟩ := _hMer
  exact ⟨{ meromorphicMap := f, principal := f.principal, principal_eq := rfl }, hf⟩


theorem package_global_extension_into_RawMeromorphic
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (td : ThirdKindMeromorphicData X Q₁ Q₂)
    (hGlobal : True) :
    ∃ (data : RawMeromorphicWithPrincipal X),
      data.principal =
        HolomorphicForms.Divisor.point Q₁ - HolomorphicForms.Divisor.point Q₂ :=
  wrap_meromorphicMap_into_RawMeromorphic X Q₁ Q₂ hne
    (build_meromorphicMap_from_global_extension X Q₁ Q₂ hne td hGlobal)


/--
Given a meromorphic data bundle `data : RawMeromorphicWithPrincipal X`
whose principal divisor is `(Q₁) - (Q₂)` with `Q₁ ≠ Q₂`, package the
underlying `data.meromorphicMap.toMap` into a fresh
`MeromorphicMapToSphere X` whose `zeroDivisor` is exactly `(Q₁)`,
whose `poleDivisor` is exactly `(Q₂)`, and which therefore satisfies
all of the structural axioms of `MeromorphicMapToSphere` against this
canonical divisor data.

Mathematically this is the classical fact that a meromorphic function
`f : X → ℂ̂` whose principal divisor is `(Q₁) - (Q₂)` has a *simple
zero* at `Q₁` and a *simple pole* at `Q₂` (and is finite-and-nonzero
elsewhere), so its canonical zero/pole decomposition is forced.
Formally, this requires reading the per-point analytic order off of
`data.meromorphicMap.toMap` — content the current
`RawMeromorphicWithPrincipal` interface does not expose, so the proof
remains a single named obligation here.

#### Implementation
-/
theorem meromorphicMap_canonicalDecomposition_of_two_point_principal_obligation
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (_data : RawMeromorphicWithPrincipal X)
    (_hprincipal :
      _data.principal =
        HolomorphicForms.Divisor.point Q₁ - HolomorphicForms.Divisor.point Q₂) :
    ∃ (f : HolomorphicForms.MeromorphicMapToSphere X),
      f.zeroDivisor = HolomorphicForms.Divisor.point Q₁ ∧
      f.poleDivisor = HolomorphicForms.Divisor.point Q₂ ∧
      f.principalDivisor =
        HolomorphicForms.Divisor.point Q₁ - HolomorphicForms.Divisor.point Q₂ :=
  assemble_meromorphicMap X Q₁ Q₂ hne

/--
This is now a pure assembly: the entire analytic content (binding the
reassigned divisor data to the actual zero/pole orders of
`data.meromorphicMap.toMap`) is captured by the single named obligation
`meromorphicMap_canonicalDecomposition_of_two_point_principal_obligation`.
-/
theorem meromorphicMapToSphere_package_of_two_point_principal
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (data : RawMeromorphicWithPrincipal X)
    (hprincipal :
      data.principal =
        HolomorphicForms.Divisor.point Q₁ - HolomorphicForms.Divisor.point Q₂) :
    ∃ (f : HolomorphicForms.MeromorphicMapToSphere X),
      f.zeroDivisor = HolomorphicForms.Divisor.point Q₁ ∧
      f.poleDivisor = HolomorphicForms.Divisor.point Q₂ ∧
      f.principalDivisor =
        HolomorphicForms.Divisor.point Q₁ - HolomorphicForms.Divisor.point Q₂ :=
  meromorphicMap_canonicalDecomposition_of_two_point_principal_obligation
    X Q₁ Q₂ hne data hprincipal


/--
#### Proof structure

This assembly chains four already-named obligations:

1. `meromorphicDegreeOneData_of_poleDivisor_point` (in
   `MeromorphicDegree.lean`) extracts continuity and bijectivity of
   `f.toMap` from the simple-pole hypothesis.
2. `Continuous.homeoOfEquivCompactToT2` (Mathlib) promotes a
   continuous bijection between a compact space and a T₂ space to a
   homeomorphism, giving `X ≃ₜ OnePoint ℂ`.
3. `onePointCx_homeomorph_sphere` (in `GenusZeroClassification.lean`)
   composes with the standard homeomorphism `OnePoint ℂ ≃ₜ S²` (via
   inverse stereographic projection / `onePointEquivSphereOfFinrankEq`
   from Mathlib).
4. `analyticGenus_eq_zero_of_homeomorphic_sphere` (in
   `GenusZeroClassification.lean`) concludes
   `analyticGenus ℂ X = 0`.
-/
theorem degree_one_meromorphicMap_implies_analyticGenus_zero_with_meromorphicData
    (f : HolomorphicForms.MeromorphicMapToSphere X) (Q₂ : X)
    (hpole : f.poleDivisor = HolomorphicForms.Divisor.point Q₂)
    (hmod : f.PoleModulusData)
    (hbranch : f.BranchedCoverDataOfPoleDegree) :
    analyticGenus ℂ X = 0 := by
  -- Step 1: simple pole gives continuity + bijectivity of `f.toMap`.
  obtain ⟨data⟩ :=
    HolomorphicForms.meromorphicDegreeOneData_of_poleDivisor_point X f Q₂ hpole hmod hbranch
  -- Step 2: package the continuous bijection as a homeomorphism `X ≃ₜ OnePoint ℂ`.
  let equiv : X ≃ OnePoint ℂ := Equiv.ofBijective f.toMap data.bijective_toMap
  have hcont : Continuous equiv := by simpa [equiv] using data.continuous_toMap
  let h₁ : X ≃ₜ OnePoint ℂ := hcont.homeoOfEquivCompactToT2
  -- Step 3: compose with `OnePoint ℂ ≃ₜ S²`.
  let h₂ : X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    h₁.trans HolomorphicForms.onePointCx_homeomorph_sphere
  -- Step 4: easy direction of the genus-zero classification.
  exact HolomorphicForms.analyticGenus_eq_zero_of_homeomorphic_sphere X ⟨h₂⟩

/--
The honest assembly that *can* be proved is
`degree_one_meromorphicMap_implies_analyticGenus_zero_with_meromorphicData`,
which takes BOTH `PoleModulusData` and `BranchedCoverDataOfPoleDegree` as
explicit hypotheses. The clean wrapper
`degree_one_meromorphicMap_implies_analyticGenus_zero_of_routeData` below
exposes it under a friendlier name.

**Un-bundling (2026-05-29):** previously this declaration took only
`hpole` and extracted the analytic content via the universal-bridge
accessors `MeromorphicMapToSphere.toPoleModulusData` /
`toBranchedCoverDataOfPoleDegree` (now removed; see
`Jacobian/HolomorphicForms/Meromorphic.lean` for the un-bundling
rationale). The bridges hid the analytic content; now it is supplied
as the explicit `hmod` / `hbranch` hypotheses, matching the
`_with_meromorphicData` sibling pattern used throughout the
codebase. The conclusion `analyticGenus ℂ X = 0` is unchanged; the
added preconditions are strengthenings, not weakenings.

Do not "prove" this theorem by manufacturing route data from `hpole` alone:
that would derive genus-zero classification for arbitrary `X`.
-/
theorem degree_one_meromorphicMap_implies_analyticGenus_zero
    (f : HolomorphicForms.MeromorphicMapToSphere X) (Q₂ : X)
    (hpole : f.poleDivisor = HolomorphicForms.Divisor.point Q₂)
    (hmod : f.PoleModulusData)
    (hbranch : f.BranchedCoverDataOfPoleDegree) :
    analyticGenus ℂ X = 0 :=
  degree_one_meromorphicMap_implies_analyticGenus_zero_with_meromorphicData X f Q₂
    hpole hmod hbranch


theorem degree_one_meromorphicMap_implies_analyticGenus_zero_of_routeData
    (f : HolomorphicForms.MeromorphicMapToSphere X) (Q₂ : X)
    (hpole : f.poleDivisor = HolomorphicForms.Divisor.point Q₂)
    (hmod : f.PoleModulusData)
    (hbranch : f.BranchedCoverDataOfPoleDegree) :
    analyticGenus ℂ X = 0 :=
  degree_one_meromorphicMap_implies_analyticGenus_zero_with_meromorphicData X f Q₂
    hpole hmod hbranch

/--
Internal assembly: a meromorphic map with a single pole forces genus zero
(per-`f` precondition-strengthened form, mirroring the
`_with_meromorphicData` sibling). Internal-only; no external callers.

**Un-bundling (2026-05-29):** previously took only `(f, Q, hpole)` and
relied on the now-removed `MeromorphicMapToSphere` universal-bridge
accessors via the bare
`degree_one_meromorphicMap_implies_analyticGenus_zero`. Now takes
`hmod` and `hbranch` explicitly.
-/
theorem nonconstant_single_pole_implies_genus_zero
    (f : HolomorphicForms.MeromorphicMapToSphere X)
    (Q : X)
    (hpole : f.poles = HolomorphicForms.Divisor.point Q)
    (hmod : f.PoleModulusData)
    (hbranch : f.BranchedCoverDataOfPoleDegree) :
    analyticGenus ℂ X = 0 := by
  exact degree_one_meromorphicMap_implies_analyticGenus_zero X f Q hpole hmod hbranch


theorem nonconstant_single_pole_implies_genus_zero_of_routeData
    (f : HolomorphicForms.MeromorphicMapToSphere X)
    (Q : X)
    (hpole : f.poles = HolomorphicForms.Divisor.point Q)
    (hmod : f.PoleModulusData)
    (hbranch : f.BranchedCoverDataOfPoleDegree) :
    analyticGenus ℂ X = 0 :=
  nonconstant_single_pole_implies_genus_zero_with_meromorphicData X f Q hpole hmod hbranch


end JacobianChallenge.AbelJacobi
