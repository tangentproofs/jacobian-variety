import Jacobian.HolomorphicForms.TraceSpec
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Jacobian.Blueprint.Sec02.BranchedDegreeFromHolomorphic
import Jacobian.ComplexTorus.Smul
import Jacobian.AbelJacobi.AnalyticOfCurveBasis
import Jacobian.ComplexTorus.OfClm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option linter.unusedSectionVars false

/-!
# Analytic degree and the trace–pullback identity

The degree of a holomorphic map between compact Riemann surfaces, in
its analytic incarnation, plus the trace–pullback identity that
underlies `Jacobian/Solution.lean`'s `pushforward_pullback` lemma.

Named obligations:

* `analyticDegree f hf` — the degree of `f` (concrete ℕ-valued
  definition: `0` if `f` is constant or if no compatible branched-cover
  datum exists; otherwise the `branchedDegree` of a Classically chosen
  compatible witness);
* `analyticPushforward_analyticPullback` — the trace–pullback
  identity, in basis-aligned form:
  `analyticPushforward (analyticPullback Q) = analyticDegree • Q`.

Bottom-up content: degree is the generic-fiber cardinality (with
ramification multiplicity); the trace–pullback identity is the
classical `tr_f (f* η) = deg(f) · η` for holomorphic 1-forms,
descended through the period quotient.
-/

namespace JacobianChallenge.TraceDegree

open scoped ContDiff Manifold
open JacobianChallenge.AbelJacobi JacobianChallenge.Periods
open JacobianChallenge.HolomorphicForms

variable {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms ℂ X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
  [JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms ℂ Y]

/--
**Concrete analytic degree.** For a smooth map `f : X → Y` of
compact Riemann surfaces, the degree is:

* `0` if `f` is constant;
* `branchedDegree hbc` for a Classically chosen `RamificationIndexCompatible`
  branched-cover datum `hbc`, if such a witness exists;
* `0` otherwise.
-/
noncomputable def analyticDegree (f : X → Y)
    (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  open Classical in
  if _hconst : ∃ y₀, ∀ x, f x = y₀ then 0
  else
    if hbc : ∃ hbc : BranchedCoverData X Y f,
        hbc.RamificationIndexCompatible then
      branchedDegree hbc.choose
    else 0


@[simp]
theorem analyticDegree_constant (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hconst : ∃ y₀, ∀ x, f x = y₀) :
    analyticDegree f hf = 0 := by
  unfold analyticDegree
  simp [hconst]

/--
**Branched-degree-uniqueness for holomorphic maps.** Two
`RamificationIndexCompatible` branched-cover data on the same
holomorphic map have equal `branchedDegree`.

This is the load-bearing technical lemma making `analyticDegree`
well-defined independently of the Classical choice of witness: any
two compatible witnesses give the same branched degree, because their
`ramificationIndex` functions both equal `mapAnalyticOrderAt f` on the
(entire) holomorphic locus, and the finite-fiber `toFinset`s depend
only on the set.
-/
theorem branchedDegree_eq_of_compatible
    {f : X → Y} (hHol : IsHolomorphic f)
    (h₁ h₂ : BranchedCoverData X Y f)
    (hc₁ : h₁.RamificationIndexCompatible)
    (hc₂ : h₂.RamificationIndexCompatible) :
    branchedDegree h₁ = branchedDegree h₂ := by
  classical
  -- Pick any base point on Y
  set y : Y := Classical.arbitrary Y
  rw [branchedDegree_eq_weightedFiberCard h₁ y,
      branchedDegree_eq_weightedFiberCard h₂ y]
  -- Both equal a sum over the finite fibre toFinset; the toFinset only
  -- depends on the underlying set, so the two toFinsets agree.
  unfold BranchedCoverData.weightedFiberCard
  have hfin_eq : (h₁.finite_fiber y).toFinset = (h₂.finite_fiber y).toFinset :=
    Set.Finite.toFinset_inj.mpr rfl
  rw [hfin_eq]
  refine Finset.sum_congr rfl ?_
  intro x _
  -- ramificationIndex x = mapAnalyticOrderAt f x on both sides (compatibility + holomorphicity).
  rw [hc₁ x (hHol.holomorphicAt x), hc₂ x (hHol.holomorphicAt x)]

/--
**Analytic degree equals branched degree, canonical form.** For a
nonconstant smooth map of compact Riemann surfaces, the analytic degree
agrees with the branched degree of **any** `RamificationIndexCompatible`
branched-cover datum on `f` (provided `f` is holomorphic, which is
automatic from smoothness via the kfold package).
-/
theorem analyticDegree_eq_canonical_branchedDegree (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hHol : IsHolomorphic f)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀) :
    analyticDegree f hf = branchedDegree hbc := by
  classical
  unfold analyticDegree
  simp only [dif_neg hnonconst]
  -- The existence witness is nonempty: hbc itself.
  have hex : ∃ hbc' : BranchedCoverData X Y f,
      hbc'.RamificationIndexCompatible := ⟨hbc, hcompat⟩
  simp only [dif_pos hex]
  -- Compare Classical.choose with hbc via branched-degree uniqueness.
  exact branchedDegree_eq_of_compatible hHol _ hbc hex.choose_spec hcompat

omit [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [IsManifold 𝓘(ℂ) ω X]
  [T2Space Y] [CompactSpace Y] [IsManifold 𝓘(ℂ) ω Y] in
/--
**Analytic degree identity, explicit form (legacy wrapper).** The
equality between the analytic degree and a supplied branched-cover
degree, given the equation as a hypothesis. New callers should prefer
`analyticDegree_eq_canonical_branchedDegree`.
-/
theorem analyticDegree_eq_branchedDegree (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hbc : JacobianChallenge.HolomorphicForms.BranchedCoverData X Y f)
    (hdegree : analyticDegree f hf = JacobianChallenge.HolomorphicForms.branchedDegree hbc) :
    analyticDegree f hf =
      JacobianChallenge.HolomorphicForms.branchedDegree hbc := hdegree

/--
Trace-degree consumers no longer carry a provider-local analytic gap;
the remaining analytic content lives where it belongs, in
`HolomorphicMap.lean`.
-/
theorem hasWeightedFiberConservation_provider (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HasWeightedFiberConservation f :=
  hasWeightedFiberConservation_of_contMDiff hf

/--
**The narrow trace regularity provider.** Global trace of
holomorphic 1-forms agrees with the regular-value local trace formula.
-/
noncomputable def traceFormsRegularSpec_provider (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    TraceFormsRegularSpec f hf where
  map_zero := by
    change (traceFormsConstructionData_provider f hf 0).traceForm = 0
    exact (traceFormsConstructionData_provider f hf 0).map_zero_spec rfl
  apply_fun_regular := by
    intro hbc hcompat η y hy
    change (traceFormsConstructionData_provider f hf η).traceForm.toFun y = _
    exact (traceFormsConstructionData_provider f hf η).regular_spec hbc hcompat y hy

/--
Assembled here from four narrow inputs, the same shape as
`trace_pullback_identity_of_spec` in `TraceBundled.lean`:
* `traceFormsRegularSpec_provider` — regular-value trace formula;
* `hasLocalKfoldRamification_of_contMDiff` — local k-fold ramification;
* `hasWeightedFiberConservation_provider` — weighted-fiber conservation;
* `analyticDegree_eq_canonical_branchedDegree` — degree normalisation.

The mirror assembly `trace_pullback_identity_of_spec` in
`TraceBundled.lean` takes the same shape but with an explicit
`TraceFormsRegularSpec` boundary; here the trace spec is supplied via
the named provider so callers can use the identity uniformly with the
provider-based interface.
-/
noncomputable def trace_pullback_provider (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) :
    traceFormsBundled f hf (pullbackFormsBundled f hf η) =
      (analyticDegree f hf : ℂ) • η := by
  classical
  set htrace : TraceFormsRegularSpec f hf := traceFormsRegularSpec_provider f hf with htrace_def
  set hkfold : HasLocalKfoldRamification f := hasLocalKfoldRamification_of_contMDiff hf
    with hkfold_def
  set hw : HasWeightedFiberConservation f := hasWeightedFiberConservation_provider f hf
    with hw_def
  have hHol : IsHolomorphic f := isHolomorphic_of_contMDiff hf hkfold
  by_cases hconst : ∃ y₀, ∀ x, f x = y₀
  · -- Constant case: both sides are zero.
    have hpb_zero : pullbackFormsBundled f hf η = 0 := by
      apply ContMDiffSection.coe_inj
      funext x
      obtain ⟨y₀, hf_const⟩ := hconst
      have hf_eq : f = fun _ : X => y₀ := funext hf_const
      subst f
      simp [pullbackFormsBundled, pullbackFormsFunFiber, mfderiv_const]
    rw [hpb_zero, htrace.map_zero, analyticDegree_constant f hf hconst]
    apply ContMDiffSection.ext
    intro y
    simp
  · -- Nonconstant case: descend through the regular locus by the identity principle.
    set hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
      hHol hw hconst with hbc_def
    have hcompat : hbc.RamificationIndexCompatible :=
      JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
        hHol hw hconst
    have hdeg : analyticDegree f hf = branchedDegree hbc :=
      analyticDegree_eq_canonical_branchedDegree f hf hHol hbc hcompat hconst
    rw [hdeg]
    apply holomorphicOneForm_ext_on (regularLocus_dense hbc)
    intro y hy
    rw [branchedDegree_eq_weightedFiberCard hbc y,
        htrace.apply_fun_regular hbc hcompat (pullbackFormsBundled f hf η) y hy]
    exact trace_pullback_at_regular_value hbc hcompat hf hHol η y hy

/--
**Linear trace-pullback identity.** The trace of the pullback of a
holomorphic 1-form (both viewed as linear maps) is degree
multiplication.
-/
theorem traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (traceFormsBundledLM f hf).comp (pullbackFormsBundledLM X Y f hf) =
      (analyticDegree f hf : ℂ) • LinearMap.id := by
  apply LinearMap.ext
  intro η
  show traceFormsBundledLM f hf (pullbackFormsBundledLM X Y f hf η) =
    (analyticDegree f hf : ℂ) • η
  -- traceFormsBundledLM is the linear-map shim around traceFormsBundled;
  -- pullbackFormsBundledLM is the linear-map shim around pullbackFormsBundled.
  show traceFormsBundled f hf (pullbackFormsBundled f hf η) = _
  exact trace_pullback_provider f hf η


end JacobianChallenge.TraceDegree
