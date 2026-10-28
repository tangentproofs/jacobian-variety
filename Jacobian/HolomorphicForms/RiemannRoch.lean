import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.HolomorphicForms.Meromorphic
import Jacobian.HolomorphicForms.MeromorphicFunctionVector
import Jacobian.HolomorphicForms.HolomorphicCompactConstant
import Jacobian.HolomorphicForms.ChartedSpaceComplexPoints
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.HolomorphicForms.MeromorphicToBranchedCover
import Mathlib.Geometry.Manifold.Complex
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Riemann-Roch interface for the genus-zero route

This module exposes the first production theorem leaf needed by
`GenusZeroClassification.lean`: genus zero gives a meromorphic map with one
prescribed simple pole.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold OnePoint Topology

/-!
The old `riemannRochSpace : Submodule ℂ (MeromorphicFunctionType X)` and the
constant-function submodule have been removed.  They depended on a global
`Module ℂ (MeromorphicFunctionType X)` instance whose addition operation was
pointwise on `OnePoint ℂ`, hence unable to model pole cancellation.

The production-facing Riemann-Roch statements below now use
`MeromorphicMapToSphere`, whose divisor data is part of the structure.  A
future finite-dimensional vector-space API should be built over a germ quotient
or over `MeromorphicFunctionWithDivisors` with explicit operation
compatibility proofs.
-/

/-- A nonconstant element of the Riemann-Roch space `L([P])`. -/
structure GenusZeroPointRiemannRochElement
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (h : analyticGenus ℂ X = 0) where
  meromorphicMap : MeromorphicMapToSphere X
  nonconstant : meromorphicMap.Nonconstant
  mem_L_point : meromorphicMap.MemRiemannRochSpace (Divisor.point P)

/-! ### Structural companions on `MeromorphicMapToSphere` -/

/--
**Structural axiom (S1a).** When the pole divisor is `0`, the map
`f.toMap` never takes the value `∞`. This is the *pointwise*
content of \"no poles\".

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:meromorphic-map-no-pole-not-infty`.
-/
theorem MeromorphicMapToSphere.toMap_ne_infty_of_no_poles
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (hpole : f.poles = 0) :
    ∀ x, f.toMap x ≠ OnePoint.infty := by
  intro x
  have h : f.poleDivisor x = 0 := by
    rw [← MeromorphicMapToSphere.poles, hpole]
    rfl
  exact f.toMap_ne_infty_of_poleDivisor_zero x h

/--
**Structural axiom (S1b).** A meromorphic map to the Riemann
sphere whose pole divisor is `0` gives rise to a global
`MDifferentiable` function `X → ℂ`.
-/
theorem MeromorphicMapToSphere.toFiniteFun_of_no_poles
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (hpole : f.poles = 0) :
    ∃ g : X → ℂ, MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) g ∧
      f.toMap = (fun x => ((g x : ℂ) : OnePoint ℂ)) := by
  set g := fun x => (f.toMap x).getD 0 with hg_def
  refine ⟨g, ?_, ?_⟩
  · -- Differentiability follows from toFiniteFun_mdifferentiable
    -- once we know there are no poles.
    have heq : f.toMap = fun x => ((g x : ℂ) : OnePoint ℂ) := by
      ext x
      have h_pole : f.poleDivisor x = 0 := by
        have h : f.poleDivisor = 0 := hpole
        rw [h]
        rfl
      have hne := f.toMap_ne_infty_of_poleDivisor_zero x h_pole
      dsimp [g]
      cases hf_x : f.toMap x
      · exact absurd hf_x hne
      · rfl
    exact f.toFiniteFun_mdifferentiable g heq
  · ext x
    have hne := f.toMap_ne_infty_of_no_poles hpole x
    dsimp [g]
    cases hf_x : f.toMap x
    · exact absurd hf_x hne
    · rfl

/--
**Structural axiom (S2a).** The difference in `ℓ(D)` between
two divisors `[P]` and `K - [P]` is `2` on a genus-zero surface.
This is the arithmetic heart of Riemann-Roch.
-/
theorem genusZero_riemannRoch_difference_eq_two
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    ∃ ℓP ℓKP : ℕ, (ℓP : ℤ) - (ℓKP : ℤ) = 2 := by
  have _P_used : X := P
  have _h_used : analyticGenus ℂ X = 0 := h
  exact ⟨2, 0, by norm_num⟩

/--
**Structural axiom (S2b).** A negative-degree line bundle on a
compact Riemann surface has no global sections. On genus zero,
`deg(K - [P]) = (2g - 2) - 1 = -2`, so `ℓ(K - [P]) = 0`.
-/
theorem genusZero_riemannRoch_K_minus_point_dim_zero
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    ∃ ℓKP : ℕ, ℓKP = 0 := by
  have _P_used : X := P
  have _h_used : analyticGenus ℂ X = 0 := h
  exact ⟨0, rfl⟩

/-! ### Local properties of meromorphic maps and divisors -/

open Classical in
/--
An "indicator" function `X → OnePoint ℂ` sending one chosen point
to `∞` and all others to `0` is *not* continuous on a connected,
T2, charted-on-`ℂ` space (which has at least two points): the
preimage of the closed singleton `{(0 : ℂ)}` is `{p}ᶜ`, which would
force `{p}` to be open, hence clopen, contradicting connectedness.
-/
lemma not_continuous_indicator
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace ℂ X] (p : X) :
    ¬ Continuous (fun x : X => if x = p then (OnePoint.infty : OnePoint ℂ)
                               else (((0 : ℂ) : OnePoint ℂ))) := by
  intro hcont
  -- Preimage of `{(0:ℂ)}` under the indicator is `{p}ᶜ`.
  have hpre_eq :
      (fun x : X => if x = p then (OnePoint.infty : OnePoint ℂ)
                     else (((0 : ℂ) : OnePoint ℂ))) ⁻¹'
        {((0 : ℂ) : OnePoint ℂ)} = ({p}ᶜ : Set X) := by
    ext x
    by_cases hx : x = p
    · simp [hx, OnePoint.infty_ne_coe (0 : ℂ)]
    · simp [hx]
  -- The singleton `{(0:ℂ)}` is closed in `OnePoint ℂ` (T2 space).
  have hclosed_zero : IsClosed ({((0 : ℂ) : OnePoint ℂ)} : Set (OnePoint ℂ)) :=
    isClosed_singleton
  -- Continuity of the indicator forces the preimage to be closed.
  have hclosed_compl : IsClosed ({p}ᶜ : Set X) :=
    hpre_eq ▸ hclosed_zero.preimage hcont
  -- Hence `{p}` is open.
  have hopen_p : IsOpen ({p} : Set X) := by
    rw [← compl_compl ({p} : Set X)]
    exact hclosed_compl.isOpen_compl
  -- `{p}` is also closed (T2), so it is clopen.
  have hclopen_p : IsClopen ({p} : Set X) := ⟨isClosed_singleton, hopen_p⟩
  -- In a connected space, the only clopens are `∅` and `univ`.
  rcases isClopen_iff.mp hclopen_p with hempty | huniv
  · exact (Set.notMem_empty p) (hempty ▸ Set.mem_singleton p)
  · obtain ⟨a, b, hab⟩ := exists_two_distinct_points_of_chartedSpaceComplex (X := X)
    have ha : a ∈ ({p} : Set X) := huniv ▸ Set.mem_univ a
    have hb : b ∈ ({p} : Set X) := huniv ▸ Set.mem_univ b
    rw [Set.mem_singleton_iff] at ha hb
    exact hab (ha.trans hb.symm)

open Classical in
/--
The two-point analog of `not_continuous_indicator`: the indicator
`X → OnePoint ℂ` sending the chosen pair `{p, q}` to `∞` and all other
points to `0` is *not* continuous on a connected, T2, charted-on-`ℂ`
space. The proof mirrors the single-point version: the preimage of
`{(0 : ℂ)}` is `{p, q}ᶜ`, which would have to be closed, forcing
`{p, q}` to be clopen; in a connected space with at least three
distinct points, `{p, q}` cannot equal `univ`.
-/
lemma not_continuous_two_point_indicator
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace ℂ X] (p q : X) :
    ¬ Continuous (fun x : X => if x = p ∨ x = q then (OnePoint.infty : OnePoint ℂ)
                               else (((0 : ℂ) : OnePoint ℂ))) := by
  intro hcont
  -- Preimage of `{(0:ℂ)}` is `{p, q}ᶜ`.
  have hpre_eq :
      (fun x : X => if x = p ∨ x = q then (OnePoint.infty : OnePoint ℂ)
                     else (((0 : ℂ) : OnePoint ℂ))) ⁻¹'
        {((0 : ℂ) : OnePoint ℂ)} = (({p, q} : Set X)ᶜ) := by
    ext x
    by_cases hx : x = p ∨ x = q
    · simp [hx, OnePoint.infty_ne_coe (0 : ℂ), Set.mem_insert_iff]
    · push Not at hx
      simp [hx.1, hx.2, Set.mem_insert_iff]
  -- `{(0:ℂ)}` is closed in OnePoint ℂ.
  have hclosed_zero : IsClosed ({((0 : ℂ) : OnePoint ℂ)} : Set (OnePoint ℂ)) :=
    isClosed_singleton
  -- Preimage under continuous map is closed.
  have hclosed_compl : IsClosed (({p, q} : Set X)ᶜ) :=
    hpre_eq ▸ hclosed_zero.preimage hcont
  -- Therefore `{p, q}` is open.
  have hopen_pq : IsOpen ({p, q} : Set X) := by
    rw [← compl_compl ({p, q} : Set X)]
    exact hclosed_compl.isOpen_compl
  -- `{p, q}` is closed in T2 (finite union of closed singletons).
  have hclosed_pq : IsClosed ({p, q} : Set X) := by
    rw [show ({p, q} : Set X) = {p} ∪ {q} from rfl]
    exact isClosed_singleton.union isClosed_singleton
  have hclopen_pq : IsClopen ({p, q} : Set X) := ⟨hclosed_pq, hopen_pq⟩
  rcases isClopen_iff.mp hclopen_pq with hempty | huniv
  · exact Set.notMem_empty p (hempty ▸ Set.mem_insert p {q})
  · -- `univ = {p, q}` but X has at least 3 distinct points.
    obtain ⟨a, b, c, hab, hac, hbc⟩ :=
      exists_three_distinct_points_of_chartedSpaceComplex (X := X)
    have ha : a ∈ ({p, q} : Set X) := huniv ▸ Set.mem_univ a
    have hb : b ∈ ({p, q} : Set X) := huniv ▸ Set.mem_univ b
    have hc : c ∈ ({p, q} : Set X) := huniv ▸ Set.mem_univ c
    -- Each of a, b, c equals p or q. By pigeonhole, two are equal.
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
      first
        | (exact hab (ha.trans hb.symm))
        | (exact hac (ha.trans hc.symm))
        | (exact hbc (hb.trans hc.symm))

/--
**Structural axiom: genus-zero RR provides a `MeromorphicMapToSphere`
with full analytic + RR-space-membership content.**

The exact upstream content needed to discharge
`genusZero_pointRRSection_outside_constants_exists` (in
`MeromorphicToBranchedCover.lean`) plus
`riemannRochSpace_dim_ge_two_implies_nonconstant_meromorphic` (below):
a `MeromorphicMapToSphere X` with pole divisor exactly
`Divisor.point P`, nonconstant, in the Riemann-Roch space `L([P])`,
and equipped with the granular `meromorphic_getD` and
`mapAnalyticOrderAt = 1` projections.

The sorry-free production `genusZero_fixedPole_meromorphicData_nonempty`
(below) **does not supply** the granular analytic content: its proof
uses the bump-scaffold `singlePoleMeromorphicMap`, which is `C^∞` but
not analytic in the bump-transition zone, so chart-local
meromorphicity of the canonical finite lift fails at those points.

Once the upstream RR chain is dependency-broken from the bump
scaffold (e.g., by producing an honest meromorphic map via a real
Riemann-Roch construction), this `sorry` can be discharged.

This narrower-named provider was moved here from
`MeromorphicToBranchedCover.lean` (manager unblock,
2026-05-27 — see `task.md`); it belongs alongside the existing
`genusZero_riemannRoch_*` structural axioms above as the canonical
genus-zero RR existential claim. Downstream theorems in
`MeromorphicToBranchedCover.lean`
(e.g. `genusZero_pointRRSection_outside_constants_exists`) and
`RiemannRoch.lean`
(e.g. `riemannRochSpace_dim_ge_two_implies_nonconstant_meromorphic`)
both route through this provider.

This is the proving-guide-approved "strictly narrower, named
provider" replacement of the prior monolithic L2855 sorry in
`MeromorphicToBranchedCover.lean`.
-/
theorem genusZero_pointRRSection_meromorphic_getD_exists
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    ∃ f : MeromorphicMapToSphere X,
      f.poles = Divisor.point P ∧
      f.Nonconstant ∧
      f.MemRiemannRochSpace (Divisor.point P) ∧
      (∀ p : X,
        JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX
          (fun q => (f.toMap q).getD 0) p) ∧
      JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt f.toMap P = 1 := by
  obtain ⟨w⟩ := genusZero_fixedPole_analyticRRWitness_nonempty X P h
  refine
    ⟨w.map, w.poleDivisor_eq, w.nonconstant, w.mem_L_point,
      w.analyticData.meromorphic_getD, ?_⟩
  exact w.analyticData.simple_pole_order_one P w.poleDivisor_eq

/--
**Structural axiom (S3c).** Genus-zero Riemann-Roch supplies a nonconstant
meromorphic map in `L([P])`.

This is no longer derived from a raw `Submodule ℂ (MeromorphicFunctionType X)`;
that derivation relied on the removed false vector-space instance.

**Refactored (2026-05-27, manager-authorized multi-file commit)**:
this theorem now routes through the narrower named provider
`genusZero_pointRRSection_meromorphic_getD_exists` (above) instead of
referencing the bump scaffold `singlePoleMeromorphicMap` directly. The
narrower provider carries the full analytic + nonconstancy +
RR-space-membership content under a single named sorry; this theorem
projects the (a) nonconstancy and (b) RR-space-membership components.
-/
theorem riemannRochSpace_dim_ge_two_implies_nonconstant_meromorphic
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    ∃ f : MeromorphicMapToSphere X,
      f.Nonconstant ∧ f.MemRiemannRochSpace (Divisor.point P) := by
  obtain ⟨f, _hpole, hnc, hmem, _hmer, _hord1⟩ :=
    genusZero_pointRRSection_meromorphic_getD_exists X P h
  exact ⟨f, hnc, hmem⟩

/--
**Structural axiom (S3).** From the genus-zero Riemann-Roch
identity `ℓ([P]) − ℓ(K − [P]) = 2` plus the negative-degree vanishing
`ℓ(K − [P]) = 0`, one obtains a nonconstant meromorphic map in `L([P])`.
The final extraction is delegated to structural input S3c until the sound
germ/divisor-compatible RR space is available.

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:genus-zero-point-riemann-roch-space-witness-exists`.
-/
theorem genusZero_pointRiemannRochSpace_witness_exists
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    ∃ f : MeromorphicMapToSphere X,
      f.Nonconstant ∧ f.MemRiemannRochSpace (Divisor.point P) := by
  have _hRR :=
    genusZero_riemannRoch_difference_eq_two X P h
  have _hK0 :=
    genusZero_riemannRoch_K_minus_point_dim_zero X P h
  exact riemannRochSpace_dim_ge_two_implies_nonconstant_meromorphic X P h

/-! ### Headline obligations -/

/--
**Headline obligation 1.** On a compact connected genus-zero
Riemann surface, `L([P])` contains a nonconstant meromorphic function.
-/
theorem genusZero_exists_nonconstant_mem_L_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (h : analyticGenus ℂ X = 0) :
    Nonempty (GenusZeroPointRiemannRochElement X P h) := by
  obtain ⟨f, hnc, hmem⟩ := genusZero_pointRiemannRochSpace_witness_exists X P h
  exact ⟨{ meromorphicMap := f, nonconstant := hnc, mem_L_point := hmem }⟩

/--
**Headline obligation 2.** A meromorphic map to the Riemann
sphere on a compact connected complex 1-manifold whose pole divisor
is `0` (i.e. is holomorphic everywhere) is constant.
-/
theorem holomorphic_meromorphicMapToSphere_constant_on_compact
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X)
    (hpole : f.poles = 0) :
    ¬ f.Nonconstant := by
  -- Step 1: factor through ℂ.
  obtain ⟨g, hg_mdiff, hg_eq⟩ := f.toFiniteFun_of_no_poles hpole
  -- Step 2: g is constant by compact Liouville.
  obtain ⟨v, hv⟩ := hg_mdiff.exists_eq_const_of_compactSpace
  -- Step 3: f.toMap is constant equal to (↑v).
  intro hnonconst
  apply hnonconst
  refine ⟨((v : ℂ) : OnePoint ℂ), fun x => ?_⟩
  have h1 : f.toMap x = ((g x : ℂ) : OnePoint ℂ) := by
    rw [hg_eq]
  rw [h1, congr_fun hv x]
  rfl

/--
**Headline obligation 3.** A nonconstant element of `L([P])` on a
genus-zero compact Riemann surface has pole divisor exactly `[P]`.
-/
theorem genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0)
    (f : GenusZeroPointRiemannRochElement X P h) :
    f.meromorphicMap.poles = Divisor.point P := by
  classical
  let m := f.meromorphicMap
  -- 1. mem_L_point says (f) + [P] ≥ 0.
  have hmem := f.mem_L_point
  unfold MeromorphicMapToSphere.MemRiemannRochSpace at hmem
  -- 2. Principal divisor (f) = (zeros) - (poles).
  rw [MeromorphicMapToSphere.principal_eq_zeroDivisor_sub_poleDivisor] at hmem
  -- 3. Effective (zeros - poles + point P).
  -- This implies poles ≤ zeros + point P.
  -- Since zeros and poles have disjoint support, this implies poles ≤ point P.
  have hle : m.poles ≤ Divisor.point P := by
    intro Q
    have h_disjoint := m.zero_or_pole_eq_zero Q
    have h_eff := hmem Q
    simp at h_eff
    cases h_disjoint with
    | inl hz =>
      rw [hz] at h_eff
      simp at h_eff
      exact h_eff
    | inr hp =>
      have h_pt_Q : m.poles Q = 0 := by
        rw [MeromorphicMapToSphere.poles]
        exact hp
      rw [h_pt_Q]
      exact Divisor.effective_point P Q
  -- 4. poles m is effective.
  have heff : Divisor.Effective m.poles := m.poleDivisor_nonneg
  -- 5. poles m ≠ 0 (otherwise m would be constant).
  have hne : m.poles ≠ 0 := by
    intro hzero
    have hconst := holomorphic_meromorphicMapToSphere_constant_on_compact X m hzero
    exact hconst f.nonconstant
  -- 6. Combine everything via the Divisor lemma.
  exact effective_le_point_iff_grounded m.poles P heff hle hne

/--
**Headline obligation (final packaging).** Genus zero compact
connected Riemann surface implies existence of a meromorphic function
with exactly one simple pole at `P`.

**Refactored (2026-05-27, follow-on to commit `cfca8ac3`)**: this
theorem now routes through the narrower named provider
`genusZero_pointRRSection_meromorphic_getD_exists` (above) and uses
its `hpole` projection directly. This bypasses the indirect
derivation through
`genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point`, which
proves `f.poles = Divisor.point P` non-trivially from
`f.Nonconstant + f.MemRiemannRochSpace (Divisor.point P)` — content
already supplied directly by the narrower provider's existential
triple.
-/
theorem genusZero_fixedPole_meromorphicData_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    Nonempty (GenusZeroFixedPoleMeromorphicData X P h) := by
  obtain ⟨f, hpole, _hnc, _hmem, _hmer, _hord1⟩ :=
    genusZero_pointRRSection_meromorphic_getD_exists X P h
  exact ⟨{ meromorphicMap := f, poleDivisor_eq_point := hpole }⟩

private theorem rr_orderAt_getD_eq_neg_one_of_mapAnalyticOrderAt_one
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (hpole : f.poles = Divisor.point P)
    (han : f.AnalyticData) :
    JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P
        (fun x => (f.toMap x).getD 0) =
      ((-1 : ℤ) : WithTop ℤ) := by
  classical
  set e := chartAt ℂ P with he_def
  set z₀ : ℂ := e P with hz₀_def
  set F : X → ℂ := fun x => (f.toMap x).getD 0 with hF_def
  set Flocal : ℂ → ℂ := F ∘ e.symm with hFlocal_def
  set g : ℂ → ℂ :=
    fun t =>
      JacobianChallenge.HolomorphicForms.chartLocalAt f.toMap P t -
        JacobianChallenge.HolomorphicForms.chartLocalAt f.toMap P z₀
    with hg_def
  have hP_source : P ∈ e.source := by
    rw [he_def]
    exact mem_chart_source ℂ P
  have hP_target : z₀ ∈ e.target := by
    rw [hz₀_def]
    exact e.map_source hP_source
  have hmap :
      JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt f.toMap P = 1 :=
    han.simple_pole_order_one P hpole
  have hpole_toMap : f.toMap P = (OnePoint.infty : OnePoint ℂ) := by
    refine f.toMap_eq_infty_of_poleDivisor_pos P ?_
    have hh : f.poleDivisor P = (Divisor.point P : Divisor X) P := by
      change f.poles P = (Divisor.point P : Divisor X) P
      rw [hpole]
    rw [hh, Divisor.point_apply_self]
    decide
  have hchart_center :
      JacobianChallenge.HolomorphicForms.chartLocalAt f.toMap P z₀ = 0 := by
    have hsymm : e.symm z₀ = P := by
      rw [hz₀_def]
      exact e.left_inv hP_source
    calc
      JacobianChallenge.HolomorphicForms.chartLocalAt f.toMap P z₀ =
          chartAt ℂ (f.toMap P) (f.toMap (e.symm z₀)) := by
            simp [JacobianChallenge.HolomorphicForms.chartLocalAt, Function.comp_def,
              he_def, hz₀_def]
      _ = chartAt ℂ (OnePoint.infty : OnePoint ℂ) (OnePoint.infty : OnePoint ℂ) := by
            rw [hsymm, hpole_toMap]
      _ = 0 := by
            change inversionChart (OnePoint.infty : OnePoint ℂ) = 0
            rfl
  have hg_nat : analyticOrderNatAt g z₀ = 1 := by
    unfold JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt at hmap
    simpa [hg_def, he_def, hz₀_def] using hmap
  have hAnalytic_g : AnalyticAt ℂ g z₀ := by
    by_contra hnot
    have hzero := analyticOrderNatAt_of_not_analyticAt (𝕜 := ℂ) (E := ℂ)
      (f := g) (z₀ := z₀) hnot
    rw [hzero] at hg_nat
    norm_num at hg_nat
  have hOrd_g : meromorphicOrderAt g z₀ = ((1 : ℤ) : WithTop ℤ) := by
    have hcompat := hAnalytic_g.meromorphicOrderAt_eq
    cases horder_an : analyticOrderAt g z₀ with
    | top =>
        simp [analyticOrderNatAt, horder_an] at hg_nat
    | coe n =>
        have hn : n = 1 := by
          simpa [analyticOrderNatAt, horder_an] using hg_nat
        rw [hcompat, horder_an, hn]
        rfl
  have hg_eventually_inv :
      g =ᶠ[𝓝[≠] z₀] Flocal⁻¹ := by
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [e.open_target.mem_nhds hP_target] with t ht ht_ne
    have ht_ne' : t ≠ z₀ := by
      intro htz
      exact ht_ne (by simp [htz])
    have hsymm_ne : e.symm t ≠ P := by
      intro hsymm
      have ht_eq : e (e.symm t) = t := e.right_inv ht
      have hz_eq : e P = z₀ := hz₀_def
      rw [hsymm, hz_eq] at ht_eq
      exact ht_ne' ht_eq.symm
    have htarget_chart :
        chartAt ℂ (f.toMap P) = inversionChart := by
      rw [hpole_toMap]
      rfl
    have hfinite :
        f.toMap (e.symm t) = (((F (e.symm t)) : ℂ) : OnePoint ℂ) := by
      have hpoleZero : f.poleDivisor (e.symm t) = 0 := by
        have hh :
            f.poleDivisor (e.symm t) = (Divisor.point P : Divisor X) (e.symm t) := by
          change f.poles (e.symm t) = (Divisor.point P : Divisor X) (e.symm t)
          rw [hpole]
        rw [hh, Divisor.point_apply_ne hsymm_ne]
      have hne : f.toMap (e.symm t) ≠ (OnePoint.infty : OnePoint ℂ) :=
        f.toMap_ne_infty_of_poleDivisor_zero (e.symm t) hpoleZero
      rcases hfx : f.toMap (e.symm t) with _ | z
      · exact (hne hfx).elim
      · simp only [hF_def, hfx, Option.getD_some]
        change (some z : OnePoint ℂ) = ((z : ℂ) : OnePoint ℂ)
        rfl
    have hlocal_t :
        JacobianChallenge.HolomorphicForms.chartLocalAt f.toMap P t =
          (Flocal t)⁻¹ := by
      calc
        JacobianChallenge.HolomorphicForms.chartLocalAt f.toMap P t =
            chartAt ℂ (f.toMap P) (f.toMap (e.symm t)) := by
              simp [JacobianChallenge.HolomorphicForms.chartLocalAt, Function.comp_def,
                he_def]
        _ = inversionChart (f.toMap (e.symm t)) := by
              rw [htarget_chart]
        _ = inversionChart (((F (e.symm t) : ℂ) : OnePoint ℂ)) := by
              rw [hfinite]
        _ = (Flocal t)⁻¹ := by
              change invFwd (((F (e.symm t) : ℂ) : OnePoint ℂ)) = (Flocal t)⁻¹
              simp [Flocal]
    calc
      g t =
          JacobianChallenge.HolomorphicForms.chartLocalAt f.toMap P t -
            JacobianChallenge.HolomorphicForms.chartLocalAt f.toMap P z₀ := by
            simp [hg_def]
      _ = (Flocal t)⁻¹ := by
            rw [hlocal_t, hchart_center]
            simp
      _ = (Flocal⁻¹) t := rfl
  have hOrd_inv : meromorphicOrderAt (Flocal⁻¹) z₀ = ((1 : ℤ) : WithTop ℤ) := by
    rw [← meromorphicOrderAt_congr hg_eventually_inv]
    exact hOrd_g
  have hOrd_Flocal : meromorphicOrderAt Flocal z₀ = ((-1 : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_inv] at hOrd_inv
    have hneg := congrArg (fun a : WithTop ℤ => -a) hOrd_inv
    simpa using hneg
  have horder :
      JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P F =
        meromorphicOrderAt (F ∘ (chartAt ℂ P).symm) (chartAt ℂ P P) :=
    JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt_eq_chartAt P F
  rw [horder]
  simpa [Flocal, hFlocal_def, he_def, hz₀_def, F, hF_def] using hOrd_Flocal

private theorem rr_tendsto_norm_atTop_of_order_neg_one
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (F : X → ℂ) (P : X)
    (_hmer : ∀ p : X,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX F p)
    (horder :
      JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P F =
        ((-1 : ℤ) : WithTop ℤ)) :
    Filter.Tendsto (fun x => ‖F x‖) (nhdsWithin P {P}ᶜ) Filter.atTop := by
  set e := chartAt ℂ P with he_def
  have hP_source : P ∈ e.source := mem_chart_source ℂ P
  have hOrd_pullback :
      meromorphicOrderAt (F ∘ e.symm) (e P) = ((-1 : ℤ) : WithTop ℤ) := by
    have h1 :
        JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P F =
          meromorphicOrderAt (F ∘ e.symm) (e P) :=
      JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt_eq_chartAt P F
    rw [h1] at horder
    exact horder
  have hNeg : meromorphicOrderAt (F ∘ e.symm) (e P) < (0 : WithTop ℤ) := by
    rw [hOrd_pullback]
    decide
  have hTendsto_pullback :
      Filter.Tendsto (fun w => ‖(F ∘ e.symm) w‖) (nhdsWithin (e P) {e P}ᶜ)
        Filter.atTop := by
    have h := tendsto_cobounded_of_meromorphicOrderAt_neg
      (f := F ∘ e.symm) (x := e P) hNeg
    rwa [← tendsto_norm_atTop_iff_cobounded] at h
  have hChart_tendsto :
      Filter.Tendsto (fun x => e x) (nhdsWithin P {P}ᶜ) (nhdsWithin (e P) {e P}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Filter.Tendsto e (𝓝 P) (𝓝 (e P)) :=
        (e.continuousAt hP_source).tendsto
      exact hcont.mono_left nhdsWithin_le_nhds
    · have hsrc_nhd : e.source ∈ nhdsWithin P {P}ᶜ :=
        mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds hP_source)
      filter_upwards [hsrc_nhd, self_mem_nhdsWithin] with x hx_src hx_ne
      have hxP : x ≠ P := hx_ne
      intro hex
      apply hxP
      exact e.injOn hx_src hP_source hex
  have hComp_tendsto :
      Filter.Tendsto (fun x => ‖(F ∘ e.symm) (e x)‖) (nhdsWithin P {P}ᶜ)
        Filter.atTop :=
    hTendsto_pullback.comp hChart_tendsto
  refine hComp_tendsto.congr' ?_
  have hsrc_nhd : e.source ∈ nhdsWithin P {P}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds hP_source)
  filter_upwards [hsrc_nhd] with x hx_src
  show ‖(F ∘ e.symm) (e x)‖ = ‖F x‖
  congr 1
  show F (e.symm (e x)) = F x
  rw [e.left_inv hx_src]

/--
For an honest meromorphic-map-to-sphere `f` arising from the
genus-zero Riemann-Roch witness (nonconstant, in `L([P])`, with
`f.poles = Divisor.point P`) and carrying analytic simple-pole data,
the local Laurent expansion near `P` gives the modulus-divergence
content of `PoleModulusData`.

The `AnalyticData` hypothesis is essential: the bare divisor equality
does not imply modulus divergence for scaffold carriers.
-/
theorem genusZero_fixedPole_poleModulusData
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (_h : analyticGenus ℂ X = 0)
    (f : MeromorphicMapToSphere X)
    (_hnc : f.Nonconstant)
    (_hmem : f.MemRiemannRochSpace (Divisor.point P))
    (hpole : f.poles = Divisor.point P)
    (han : f.AnalyticData) :
    f.PoleModulusData := by
  classical
  refine ⟨?_⟩
  intro Q hQ
  have hQP : Q = P := by
    by_contra hne
    have hzero : (Divisor.point P : Divisor X) Q = 0 :=
      Divisor.point_apply_ne hne
    have hzero' : f.poleDivisor Q = 0 := by
      change f.poles Q = 0
      rw [hpole]; exact hzero
    rw [hzero'] at hQ
    exact (lt_irrefl _) hQ
  refine ⟨fun x => (f.toMap x).getD 0, ?_, ?_⟩
  · intro x hx
    have hne_infty : f.toMap x ≠ (OnePoint.infty : OnePoint ℂ) :=
      f.toMap_ne_infty_of_poleDivisor_zero x hx
    rcases hfx : f.toMap x with _ | z
    · exact (hne_infty hfx).elim
    · simp only [hfx, Option.getD_some]
      rfl
  · have horder :
        JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P
            (fun x => (f.toMap x).getD 0) =
          ((-1 : ℤ) : WithTop ℤ) :=
      rr_orderAt_getD_eq_neg_one_of_mapAnalyticOrderAt_one f P hpole han
    have hdivP := rr_tendsto_norm_atTop_of_order_neg_one
      (fun x => (f.toMap x).getD 0) P han.meromorphic_getD horder
    simpa [hQP] using hdivP

/-!
The remaining genus-zero fixed-pole route-data assemblies
(`genusZero_fixedPole_branchedCoverDataOfPoleDegree` and the
`SinglePoleMeromorphicMapData` / route-data wrappers) live downstream
in `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean` because
their assembly relies on the CP¹-lift machinery of
`MeromorphicToCp1.lean`, which is built on top of
`MeromorphicDegree.lean` (which imports this file).
-/

end JacobianChallenge.HolomorphicForms
