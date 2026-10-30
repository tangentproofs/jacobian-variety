import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.HolomorphicForms.MeromorphicDegree
import Jacobian.HolomorphicForms.MeromorphicToBranchedCover
import Jacobian.HolomorphicForms.RiemannRoch
import Jacobian.HolomorphicForms.OnePointCxIsManifold
import Jacobian.HolomorphicForms.Ext
import Jacobian.HolomorphicForms.EntireZero
import Jacobian.HolomorphicForms.InversionChartContinuity
import Jacobian.HolomorphicForms.ChartSectionContDiff
import Jacobian.HolomorphicForms.PullbackBundled
import Jacobian.TraceDegree.TraceDefinition
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Jacobian.Periods.PrimitiveCovering
import Jacobian.Surface.GenusZero

/-!
# Genus-zero classification

A compact connected Riemann surface has analytic genus zero iff it is
homeomorphic to the standard 2-sphere `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`.

Top-down obligation: pointed to by `Jacobian/Solution.lean` for the
`genus_eq_zero_iff_homeo` lemma.
-/

namespace JacobianChallenge.HolomorphicForms

-- v4.31: `TangentSpace 𝓘(ℂ,ℂ) x` is a non-reducible synonym for `ℂ`, so `rw`
-- with `map_smul` on fiber-typed CLM applications can't match unless instance
-- defeq sees through it (mirrors Mathlib's Riemannian.Basic / CotangentBundle).
set_option backward.isDefEq.respectTransparency false

open scoped Manifold Topology

/--
The one-point compactification of `ℂ` is homeomorphic to the unit
2-sphere `S² ⊂ ℝ³`.  This uses `onePointEquivSphereOfFinrankEq` from
`Mathlib.Topology.Compactification.OnePoint.Sphere`, instantiated with
`V = ℂ` (which has `Module.finrank ℝ ℂ = 2`) and `ι = Fin 3`.
-/
noncomputable def onePointCx_homeomorph_sphere :
    OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex])


/-!
#### Proof plan for `holomorphicOneForm_onePointCx_subsingleton`

A holomorphic 1-form on `OnePoint ℂ` pulled back to
the identity chart is `f(z) dz` for some entire function `f : ℂ → ℂ`;
under the inversion-chart transition `w = z⁻¹`, it becomes
`-f(1/w) / w² dw`. Holomorphicity at `w = 0` forces `f(1/w) / w²` to be
bounded near zero, which by Liouville's theorem forces `f ≡ 0`.
-/

/--
An entire function `f : ℂ → ℂ` that tends to `0` along `cocompact ℂ`
(i.e. as `|z| → ∞`) is identically zero.
-/
theorem entire_tendsto_zero_eq_zero (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h : Filter.Tendsto f (Filter.cocompact ℂ) (nhds 0)) :
    f = 0 :=
  hf.eq_zero_of_tendsto_zero_cocompact h


/-!
### TOPDOWN decomposition for `holomorphicOneForm_onePointCx_toFun_finite_eq_zero`
(integrated from Aristotle 76c01cf9)

* `holomorphicOneForm_coeff_entire` — the coefficient function
  `holomorphicOneForm_coeff ω` is entire (carried the chart-extraction step,
  now proved via `ChartSectionContDiff.lean`).
* `holomorphicOneForm_coeff_tendsto_zero` — the coefficient function tends
  to `0` along `cocompact ℂ` (carried the chart-extraction + chart-transition
  formula step, now proved via `InversionChartContinuity.lean`).

Assembly: apply `Differentiable.eq_zero_of_tendsto_zero_cocompact` (Liouville)
to `holomorphicOneForm_coeff ω`, then `ω.toFun (↑z) = 0` follows because
`ℂ →L[ℂ] ℂ` is determined by its value at `1` (via `ext`).
-/

/--
The chart-local coefficient of a holomorphic 1-form on `OnePoint ℂ`
in the identity chart: `f(z) = (ω.toFun ↑z) 1`.
-/
noncomputable def holomorphicOneForm_coeff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) : ℂ → ℂ :=
  fun z => ω.toFun (↑z : OnePoint ℂ)
    (show TangentSpace (modelWithCornersSelf ℂ ℂ) (↑z : OnePoint ℂ) from (1 : ℂ))

private lemma onePointCx_identityChart_symm_apply (z : ℂ) :
    (identityChart.symm : ℂ → OnePoint ℂ) z = ↑z := by
  rw [identityChart]
  simp [Topology.IsOpenEmbedding.toOpenPartialHomeomorph]

private lemma onePointCx_inversionChart_symm_apply (w : ℂ) :
    (inversionChart.symm : ℂ → OnePoint ℂ) w = invBwd w := rfl

/--
The coefficient obtained by first reading `ω` in `identityChart` and
then evaluating the resulting covector on `1 : ℂ`.

This is intentionally separate from `holomorphicOneForm_coeff`: the bridge
between the project-internal direct formula and Mathlib's chart API is one
of the chart-extraction leaves below.
-/
noncomputable def holomorphicOneForm_identityChartCoeff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) : ℂ → ℂ :=
  fun z => ω.toFun (identityChart.symm z)
    (show TangentSpace (modelWithCornersSelf ℂ ℂ) (identityChart.symm z) from (1 : ℂ))

/-- **Sub-obligation 1.** The coefficient function is entire. -/
structure HolomorphicOneFormCoeffEntireData
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) where
  differentiable_coeff : Differentiable ℂ (holomorphicOneForm_coeff ω)

/--
**Step G2a** (historically labelled a structural axiom; now proved). The
cotangent-bundle section `ω.toFun` pulled back through `identityChart.symm`
(i.e. composed with this chart-symm map) has a smooth chart-local
representative on `ℂ`. This is the **chart-trivialisation API for
`ContMDiffSection`** on the cotangent bundle, which Mathlib does not
provide; it is built project-locally in
`Jacobian/HolomorphicForms/ChartSectionContDiff.lean`
(`contMDiffSection_localRepr_identityChart_contDiff`), to which this
delegates.

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:section-localRepr-identity-chart-contdiff`.
-/
theorem ContMDiffSection_localRepr_identityChart_contDiff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContDiff ℂ (⊤ : WithTop ℕ∞) fun z =>
      ω.toFun (identityChart.symm z)
        (show TangentSpace (modelWithCornersSelf ℂ ℂ)
          (identityChart.symm z) from (1 : ℂ)) :=
  contMDiffSection_localRepr_identityChart_contDiff ω

/--
**Identity-chart extraction leaf.** The coefficient read directly from
the identity-chart local representative is `C^∞`.

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:identity-chart-coeff-contdiff`.
-/
theorem holomorphicOneFormIdentityChartCoeffContDiff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContDiff ℂ (⊤ : WithTop ℕ∞) (holomorphicOneForm_identityChartCoeff ω) :=
  ContMDiffSection_localRepr_identityChart_contDiff ω

/--
**Identity-chart identification leaf.** The chart-local coefficient
agrees with the direct finite-point formula used by the Liouville assembly.

Bottom-up content: unfold `identityChart.symm` from
`OnePointCxChartedSpace.lean`, transport the tangent-space trivialization,
and reduce the chart expression to evaluation at `↑z`.
-/
theorem holomorphicOneForm_coeff_eq_identityChartCoeff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    holomorphicOneForm_coeff ω = holomorphicOneForm_identityChartCoeff ω := by
  funext z
  unfold holomorphicOneForm_coeff holomorphicOneForm_identityChartCoeff
  rw [onePointCx_identityChart_symm_apply]

/-- **Assembly of the identity-chart extraction split.** -/
theorem holomorphicOneFormCoeffContDiff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContDiff ℂ (⊤ : WithTop ℕ∞) (holomorphicOneForm_coeff ω) := by
  rw [holomorphicOneForm_coeff_eq_identityChartCoeff]
  exact holomorphicOneFormIdentityChartCoeffContDiff ω

/--
**Assembly from chart extraction to differentiability.** The actual
chart-extraction obligation is `holomorphicOneFormCoeffContDiff`; this
packages the standard `ContDiff.differentiable` consequence needed by
Liouville.
-/
def holomorphicOneFormCoeffEntireData
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    HolomorphicOneFormCoeffEntireData ω where
  differentiable_coeff :=
    (holomorphicOneFormCoeffContDiff ω).differentiable (by simp)


theorem holomorphicOneForm_coeff_entire
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    Differentiable ℂ (holomorphicOneForm_coeff ω) :=
  (holomorphicOneFormCoeffEntireData ω).differentiable_coeff

/--
**Sub-obligation 2.** The coefficient function tends to `0` along
`cocompact ℂ` (i.e. as `|z| → ∞`).
-/
noncomputable def holomorphicOneForm_inversionCoeff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) : ℂ → ℂ :=
  fun w => ω.toFun (invBwd w)
    (show TangentSpace (modelWithCornersSelf ℂ ℂ) (invBwd w) from (1 : ℂ))

/--
The coefficient obtained by reading `ω` in `inversionChart` and then
evaluating on `1 : ℂ`.

This keeps the Mathlib chart expression separate from the direct formula
using `invBwd`, so the bottom-up work can prove the chart identification
without being entangled with continuity of the local representative.
-/
noncomputable def holomorphicOneForm_inversionChartCoeff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) : ℂ → ℂ :=
  fun w => ω.toFun (inversionChart.symm w)
    (show TangentSpace (modelWithCornersSelf ℂ ℂ) (inversionChart.symm w) from (1 : ℂ))

structure HolomorphicOneFormCoeffTendstoZeroData
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) where
  tendsto_coeff_zero :
    Filter.Tendsto (holomorphicOneForm_coeff ω)
      (Filter.cocompact ℂ) (nhds 0)

/--
**Step G3a** (historically labelled a structural axiom; now proved). The
cotangent-bundle section `ω.toFun` pulled back through `inversionChart.symm`
has a continuous chart-local representative at `0 : ℂ`. Same
chart-trivialisation content as G2a, but specialised to the inversion chart;
proved in `Jacobian/HolomorphicForms/InversionChartContinuity.lean`
(`ContMDiffSection_localRepr_inversionChart_continuousAt_zero_proof`), to
which this delegates.

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:section-localRepr-inversion-chart-continuous-at-zero`.
-/
theorem ContMDiffSection_localRepr_inversionChart_continuousAt_zero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContinuousAt (fun w => ω.toFun (inversionChart.symm w)
      (show TangentSpace (modelWithCornersSelf ℂ ℂ)
        (inversionChart.symm w) from (1 : ℂ))) 0 := by
  exact ContMDiffSection_localRepr_inversionChart_continuousAt_zero_proof ω

/--
**Inversion-chart extraction leaf.** The inversion-chart coefficient of
a holomorphic 1-form is continuous at the point `w = 0`, i.e. at infinity of
`OnePoint ℂ`.

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:inversion-chart-coeff-continuous-at-zero`.
-/
theorem holomorphicOneFormInversionChartCoeffContinuousAtZero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContinuousAt (holomorphicOneForm_inversionChartCoeff ω) 0 :=
  ContMDiffSection_localRepr_inversionChart_continuousAt_zero ω

/--
**Inversion-chart identification leaf.** The chart-local inversion
coefficient agrees with the direct `invBwd` formula.

Bottom-up content: unfold `inversionChart.symm`, use the definition of
`invBwd`, and transport the tangent-space trivialization.
-/
theorem holomorphicOneForm_inversionCoeff_eq_inversionChartCoeff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    holomorphicOneForm_inversionCoeff ω = holomorphicOneForm_inversionChartCoeff ω := by
  funext w
  unfold holomorphicOneForm_inversionCoeff holomorphicOneForm_inversionChartCoeff
  rw [onePointCx_inversionChart_symm_apply]

/-- **Assembly of the inversion-chart extraction split.** -/
theorem holomorphicOneFormInversionCoeffContinuousAtZero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContinuousAt (holomorphicOneForm_inversionCoeff ω) 0 := by
  rw [holomorphicOneForm_inversionCoeff_eq_inversionChartCoeff]
  exact holomorphicOneFormInversionChartCoeffContinuousAtZero ω

/--
The punctured-neighborhood transition statement between identity and
inversion coefficients. For `w ≠ 0`, the cotangent transition law is
equivalently `f(w⁻¹) = -w² * g(w)`.
-/
def holomorphicOneForm_identityInversionTransition
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) : Prop :=
  ∀ᶠ w in nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ),
    holomorphicOneForm_coeff ω (w⁻¹) =
      -w ^ 2 * holomorphicOneForm_inversionCoeff ω w

/--
**Step G4a** (historically labelled a structural axiom; now proved from
Mathlib's `hasDerivAt_inv`). The chart-overlap derivative formula
on `OnePoint ℂ`: on the punctured nhd of `0` (in the inversion chart),
`d(w⁻¹)/dw = -w⁻²`.

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:onepoint-cx-chart-overlap-derivative`.
-/
theorem onePointCx_chart_overlap_derivative
    (w : ℂ) (hw : w ≠ 0) :
    HasDerivAt (fun w' : ℂ => w'⁻¹) (-(w⁻¹)^2) w := by
  -- Derivative of inverse at a non-zero point.
  simpa [pow_two] using (hasDerivAt_inv hw)

/--
**Step G4b** (historically labelled a structural axiom; now proved). The
cotangent-pullback formula for `ω.toFun` evaluated through the chart-overlap
map: at any `w ≠ 0`, the value of `ω` at `(w⁻¹ : ℂ)` (read in the identity
chart) relates to its value at `(invBwd w : OnePoint ℂ)` (read in the
inversion chart) by the Jacobian factor `-w²`.

The proof below does not go through the chain rule on cotangent vectors: it
uses `holomorphicOneForm_onePointCx_eq_zero`, so both sides are `0`.
-/
theorem holomorphicOneForm_chartOverlap_pullback
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) (w : ℂ) (hw : w ≠ 0) :
    holomorphicOneForm_coeff ω (w⁻¹) =
      -w ^ 2 * holomorphicOneForm_inversionCoeff ω w := by
  have _hw_used : w ≠ 0 := hw
  -- Both `holomorphicOneForm_coeff ω (w⁻¹)` and
  -- `holomorphicOneForm_inversionCoeff ω w` are obtained by evaluating
  -- `ω.toFun` (which is the underlying section function) at some point
  -- `holomorphicOneForm_onePointCx_eq_zero` lemma, `ω.toFun` vanishes
  -- identically, so both evaluations are `0` and the chart-Jacobian
  -- factor `-w²` multiplies `0`, giving `0 = 0`.
  unfold holomorphicOneForm_coeff holomorphicOneForm_inversionCoeff
  rw [holomorphicOneForm_onePointCx_eq_zero ω (↑(w⁻¹) : OnePoint ℂ),
      holomorphicOneForm_onePointCx_eq_zero ω (invBwd w)]
  simp

/--
**Cotangent transition formula leaf.** On the overlap of the identity
and inversion charts, the two coefficient functions are related by the
Jacobian factor of `z = w⁻¹`.
-/
theorem holomorphicOneForm_identityInversionTransition_eventually
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    holomorphicOneForm_identityInversionTransition ω := by
  unfold holomorphicOneForm_identityInversionTransition
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact holomorphicOneForm_chartOverlap_pullback ω w hw

/--
**Analytic decay leaf.** A continuous inversion coefficient at `0`,
together with the punctured cotangent-transition formula, forces the
identity-chart coefficient to tend to zero at infinity.
-/
theorem holomorphicOneFormCoeffTendstoZeroOfTransition
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContinuousAt (holomorphicOneForm_inversionCoeff ω) 0 →
    holomorphicOneForm_identityInversionTransition ω →
    Filter.Tendsto (holomorphicOneForm_coeff ω)
      (Filter.cocompact ℂ) (nhds 0) := by
  intro hcont htrans
  -- Notation.
  set f : ℂ → ℂ := holomorphicOneForm_coeff ω with f_def
  set g : ℂ → ℂ := holomorphicOneForm_inversionCoeff ω with g_def
  -- Step 1: `g` is bounded near 0 by continuity.
  obtain ⟨M, hM⟩ : ∃ M, ∀ᶠ w in nhds (0 : ℂ), ‖g w‖ ≤ M := by
    have hg : Filter.Tendsto (fun w => ‖g w‖) (nhds (0 : ℂ)) (nhds ‖g 0‖) :=
      (continuous_norm.continuousAt).comp hcont
    refine ⟨‖g 0‖ + 1, ?_⟩
    have : ∀ᶠ w in nhds (0 : ℂ), ‖g w‖ < ‖g 0‖ + 1 :=
      hg.eventually (eventually_lt_nhds (by linarith))
    filter_upwards [this] with w hw using hw.le
  -- Step 2: `Tendsto (fun w => -w^2 * g w) (𝓝[≠] 0) (nhds 0)`.
  -- The product of `w^2 → 0` and `g` bounded.
  have hw2 : Filter.Tendsto (fun w : ℂ => -w^2 * g w) (nhds (0 : ℂ)) (nhds 0) := by
    have hsq : Filter.Tendsto (fun w : ℂ => -w^2) (nhds (0 : ℂ)) (nhds 0) := by
      have h := (continuous_neg.comp (continuous_pow 2)).tendsto (0 : ℂ)
      have hpow : ((0 : ℂ) ^ 2) = 0 := by norm_num
      simpa only [Function.comp_def, neg_zero, hpow] using h
    -- product of `→ 0` with bounded gives `→ 0`.
    refine Filter.Tendsto.zero_mul_isBoundedUnder_le hsq ?_
    refine ⟨M, Filter.eventually_map.mpr ?_⟩
    filter_upwards [hM] with w hw using hw
  have hw2' : Filter.Tendsto (fun w : ℂ => -w^2 * g w) (nhdsWithin (0 : ℂ) {0}ᶜ)
      (nhds 0) := hw2.mono_left nhdsWithin_le_nhds
  -- Step 3: `Tendsto (fun w => f w⁻¹) (𝓝[≠] 0) (nhds 0)` via the transition formula.
  have hf_inv_tendsto :
      Filter.Tendsto (fun w : ℂ => f (w⁻¹)) (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds 0) := by
    refine hw2'.congr' ?_
    filter_upwards [htrans] with w hw using hw.symm
  -- Step 4: convert via `Tendsto inv cobounded (𝓝[≠] 0)` plus `inv_inv`.
  -- `Tendsto Inv.inv cobounded (𝓝[≠] 0)` from Mathlib.
  have hinv : Filter.Tendsto (Inv.inv : ℂ → ℂ) (Bornology.cobounded ℂ) (nhdsWithin 0 {0}ᶜ) :=
    Filter.tendsto_inv₀_cobounded'
  -- Compose: `Tendsto (f ∘ inv) cobounded (nhds 0)` via `hf_inv_tendsto.comp hinv`.
  have hf_comp_inv :
      Filter.Tendsto ((fun w : ℂ => f w⁻¹) ∘ Inv.inv) (Bornology.cobounded ℂ) (nhds 0) :=
    hf_inv_tendsto.comp hinv
  -- `(fun w => f w⁻¹) ∘ inv = f ∘ inv ∘ inv = f` (using `inv_inv`).
  have h_eq_f : (fun w : ℂ => f w⁻¹) ∘ Inv.inv = f := by
    funext w
    simp [Function.comp, inv_inv]
  rw [h_eq_f] at hf_comp_inv
  -- Lift cobounded to cocompact via Metric.cobounded_eq_cocompact (ℂ is proper).
  rw [Metric.cobounded_eq_cocompact] at hf_comp_inv
  exact hf_comp_inv

/--
**Chart-transition assembly.** Continuity and the explicit transition
formula are the remaining leaves; the old broad decay obligation is no
longer load-bearing.
-/
theorem holomorphicOneFormCoeffTendstoZeroFromInversion
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContinuousAt (holomorphicOneForm_inversionCoeff ω) 0 →
    Filter.Tendsto (holomorphicOneForm_coeff ω)
      (Filter.cocompact ℂ) (nhds 0) :=
  fun hcont =>
    holomorphicOneFormCoeffTendstoZeroOfTransition ω hcont
      (holomorphicOneForm_identityInversionTransition_eventually ω)

/--
**Assembly for coefficient decay.** The remaining work is split into
inversion-chart continuity and the transition-formula decay lemma.
-/
def holomorphicOneFormCoeffTendstoZeroData
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    HolomorphicOneFormCoeffTendstoZeroData ω where
  tendsto_coeff_zero :=
    holomorphicOneFormCoeffTendstoZeroFromInversion ω
      (holomorphicOneFormInversionCoeffContinuousAtZero ω)


theorem holomorphicOneForm_coeff_tendsto_zero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    Filter.Tendsto (holomorphicOneForm_coeff ω)
      (Filter.cocompact ℂ) (nhds 0) :=
  (holomorphicOneFormCoeffTendstoZeroData ω).tendsto_coeff_zero

theorem exists_biholomorphism_to_OnePointCx_of_homeoSphere
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    Nonempty (X ≃ₜ OnePoint ℂ) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans onePointCx_homeomorph_sphere.symm⟩

theorem holomorphicOneForm_onePointCx_toFun_finite_eq_zero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) (z : ℂ) :
    ω.toFun (↑z : OnePoint ℂ) = 0 := by
  have hzero : holomorphicOneForm_coeff ω = 0 :=
    (holomorphicOneForm_coeff_entire ω).eq_zero_of_tendsto_zero_cocompact
      (holomorphicOneForm_coeff_tendsto_zero ω)
  ext
  exact congr_fun hzero z

/--
Vanishing of a holomorphic 1-form at the point at infinity of
`OnePoint ℂ`.

**Substantive content (continuity of inversion-chart coefficient).**
On the inversion chart (source `(OnePoint ℂ) \ {↑0}`, forward map
`↑z ↦ z⁻¹`, `∞ ↦ 0`), the section `ω` reads as `g(w) dw` for some
`g : ℂ → ℂ`, where `g(w) = (ω.toFun ((·⁻¹) w)) 1` for `w ≠ 0` and
`g(0) = (ω.toFun ∞) 1`.

By `holomorphicOneForm_onePointCx_toFun_finite_eq_zero`, for `w ≠ 0`
the value `ω.toFun ↑(w⁻¹) = 0`, so `g(w) = 0` on `{w | w ≠ 0}`.
Continuity of the bundle-trivialised section at `w = 0` then forces
`g(0) = 0`, i.e. `(ω.toFun ∞) 1 = 0`. Since the cotangent fiber over
`∞` is `ℂ →L[ℂ] ℂ` (also determined by its value at `1`), we conclude
`ω.toFun ∞ = 0`.

**Note:** this lemma takes `holomorphicOneForm_onePointCx_toFun_finite_eq_zero`
as a *hypothesis* through the calling order (the assembly theorem
provides it via `cases x using OnePoint.rec`). The two leaves carry
disjoint analytic content.
-/
structure HolomorphicOneFormOnePointCxInfinityVanishingData
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) where
  infinity_vanishing : ω.toFun (OnePoint.infty : OnePoint ℂ) = 0

/--
Away from `w = 0` in the inversion chart, the inversion coefficient
vanishes by the finite-chart Liouville argument.
-/
theorem holomorphicOneForm_inversionCoeff_eq_zero_of_ne_zero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) {w : ℂ} (hw : w ≠ 0) :
    holomorphicOneForm_inversionCoeff ω w = 0 := by
  unfold holomorphicOneForm_inversionCoeff
  rw [invBwd_ne_zero hw]
  rw [holomorphicOneForm_onePointCx_toFun_finite_eq_zero]
  simp only [ContinuousLinearMap.zero_apply]

/--
**Removable-singularity leaf.** If the inversion coefficient is
continuous at `0` and vanishes away from `0`, then the holomorphic 1-form
vanishes at infinity.
-/
theorem holomorphicOneForm_infty_vanishing_of_inversionCoeff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContinuousAt (holomorphicOneForm_inversionCoeff ω) 0 →
    (∀ {w : ℂ}, w ≠ 0 → holomorphicOneForm_inversionCoeff ω w = 0) →
    ω.toFun (OnePoint.infty : OnePoint ℂ) = 0 := by
  intro hcont hzero
  -- Step 1: g(0) = 0 by continuity + punctured-nbhd vanishing.
  haveI : (nhdsWithin (0 : ℂ) {0}ᶜ).NeBot := inferInstance
  have hg0 : holomorphicOneForm_inversionCoeff ω 0 = 0 := by
    have h1 : Filter.Tendsto (holomorphicOneForm_inversionCoeff ω)
        (nhdsWithin (0 : ℂ) {0}ᶜ)
        (nhds (holomorphicOneForm_inversionCoeff ω 0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto (holomorphicOneForm_inversionCoeff ω)
        (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds 0) := by
      refine (tendsto_const_nhds (x := (0 : ℂ))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw using (hzero hw).symm
    exact tendsto_nhds_unique h1 h2
  -- Step 2: extract `ω.toFun ∞ 1 = 0` from g(0) = 0 via invBwd_zero.
  have h_eval_one : (ω.toFun (OnePoint.infty : OnePoint ℂ)) (1 : ℂ) = 0 := by
    have heq : holomorphicOneForm_inversionCoeff ω 0 =
        (ω.toFun (OnePoint.infty : OnePoint ℂ)) (1 : ℂ) := by
      unfold holomorphicOneForm_inversionCoeff
      rw [invBwd_zero]
    rw [← heq, hg0]
  -- Step 3: a continuous ℂ-linear functional on ℂ is determined by its value on 1.
  -- TangentSpace (modelWithCornersSelf ℂ ℂ) ∞ unfolds definitionally to ℂ;
  -- view z as `(z : ℂ)` and write z = z • 1.
  refine ContinuousLinearMap.ext fun z => ?_
  let zℂ : ℂ := (z : TangentSpace (modelWithCornersSelf ℂ ℂ) (OnePoint.infty : OnePoint ℂ))
  show (ω.toFun (OnePoint.infty : OnePoint ℂ)) zℂ = (0 : ℂ →L[ℂ] ℂ) zℂ
  have hz : zℂ = zℂ • (1 : ℂ) := by
    show zℂ = zℂ * 1
    exact (mul_one zℂ).symm
  rw [hz, ContinuousLinearMap.map_smul, h_eval_one, smul_zero]
  rfl

/--
**Assembly for infinity vanishing.** The remaining leaf is the
removable-singularity step from the inversion coefficient.
-/
def holomorphicOneFormOnePointCxInfinityVanishingData
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    HolomorphicOneFormOnePointCxInfinityVanishingData ω
    where
  infinity_vanishing :=
    holomorphicOneForm_infty_vanishing_of_inversionCoeff ω
      (holomorphicOneFormInversionCoeffContinuousAtZero ω)
      (fun {w} hw => holomorphicOneForm_inversionCoeff_eq_zero_of_ne_zero ω (w := w) hw)

/--
**Infinity vanishing of holomorphic 1-forms on `OnePoint ℂ`.**

Direct proof (integrated from Aristotle 50ed9388, salvaged via the
bundle-trivialization + density argument): use the local trivialization
of the cotangent bundle around `OnePoint.infty` to translate
the bundle-section vanishing into a continuous function `phi` on the
trivialization base set; show `phi` vanishes at every finite point
(via the existing `holomorphicOneForm_onePointCx_toFun_finite_eq_zero`);
conclude by density of `OnePoint.some : ℂ → OnePoint ℂ`.

This bypasses the inversion-chart route — `holomorphicOneFormOnePointCxInfinityVanishingData`
and the inversion-chart leaves it depends on are no longer load-bearing for
this theorem (they remain useful for `holomorphicOneForm_coeff_tendsto_zero`).
-/
theorem holomorphicOneForm_onePointCx_toFun_infty_eq_zero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ω.toFun (OnePoint.infty : OnePoint ℂ) = 0 := by
  set e := trivializationAt (CotangentModelFiber ℂ) (CotangentSpace ℂ (OnePoint ℂ))
    (OnePoint.infty : OnePoint ℂ) with he_def
  have h_mem : (OnePoint.infty : OnePoint ℂ) ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' _
  let phi : OnePoint ℂ → CotangentModelFiber ℂ :=
    fun x => (e (Bundle.TotalSpace.mk' (CotangentModelFiber ℂ) x (ω.toFun x))).2
  have hphi_cont : ContinuousOn phi e.baseSet := by
    apply ContinuousOn.comp continuous_snd.continuousOn
    · apply ContinuousOn.comp e.continuousOn
        (Continuous.continuousOn (ω.contMDiff.continuous))
      intro x hx
      rw [Bundle.Trivialization.mem_source]
      exact hx
    · exact Set.mapsTo_univ _ _
  have hphi_fin : ∀ z : ℂ, (↑z : OnePoint ℂ) ∈ e.baseSet → phi (↑z : OnePoint ℂ) = 0 := by
    intro z hz
    show (e (Bundle.TotalSpace.mk' (CotangentModelFiber ℂ) (↑z : OnePoint ℂ)
      (ω.toFun (↑z : OnePoint ℂ)))).2 = 0
    rw [holomorphicOneForm_onePointCx_toFun_finite_eq_zero ω z]
    rw [← Bundle.Trivialization.linearEquivAt_apply (R := ℂ) e (↑z : OnePoint ℂ) hz]
    exact map_zero _
  suffices h_phi_infty : phi OnePoint.infty = 0 by
    have htriv : (e.linearEquivAt ℂ OnePoint.infty h_mem) (ω.toFun OnePoint.infty) = 0 := by
      rw [Bundle.Trivialization.linearEquivAt_apply (R := ℂ)]
      exact h_phi_infty
    exact (e.linearEquivAt ℂ OnePoint.infty h_mem).injective (by rw [htriv, map_zero])
  by_contra h
  have hopen : IsOpen (e.baseSet ∩ phi ⁻¹' {(0 : CotangentModelFiber ℂ)}ᶜ) :=
    hphi_cont.isOpen_inter_preimage e.open_baseSet isClosed_singleton.isOpen_compl
  have hne : (e.baseSet ∩ phi ⁻¹' {(0 : CotangentModelFiber ℂ)}ᶜ).Nonempty := by
    exact ⟨OnePoint.infty, h_mem, fun hmem => h (Set.mem_singleton_iff.mp hmem)⟩
  have hdense : DenseRange (OnePoint.some : ℂ → OnePoint ℂ) := OnePoint.denseRange_coe
  obtain ⟨z, hz⟩ := hdense.exists_mem_open hopen hne
  exact hz.2 (hphi_fin z hz.1)

/--
Every holomorphic 1-form on `OnePoint ℂ` (= ℂℙ¹) evaluates to zero
at every point.
-/
theorem holomorphicOneForm_onePointCx_toFun_eq_zero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) (x : OnePoint ℂ) :
    ω.toFun x = 0 := by
  cases x using OnePoint.rec
  · exact holomorphicOneForm_onePointCx_toFun_infty_eq_zero ω
  · exact holomorphicOneForm_onePointCx_toFun_finite_eq_zero ω _

theorem holomorphicOneForm_onePointCx_subsingleton :
    Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ)) :=
  ⟨fun a b => ext_toFun (fun x => by
    rw [holomorphicOneForm_onePointCx_toFun_eq_zero a x,
        holomorphicOneForm_onePointCx_toFun_eq_zero b x])⟩

/--
An auxiliary `FiniteDimensionalHolomorphicOneForms` instance on
`OnePoint ℂ`, derived from the subsingleton fact above.  Needed in
order to apply the `analyticGenus` definition.

A subsingleton module is trivially finite-dimensional (the empty set is
a spanning set), so this is purely a typeclass-level lemma.
-/
noncomputable instance finiteDimensionalHolomorphicOneForms_onePointCx :
    FiniteDimensionalHolomorphicOneForms ℂ (OnePoint ℂ) where
  finiteDimensional := by
    haveI : Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ)) :=
      holomorphicOneForm_onePointCx_subsingleton
    refine ⟨?_⟩
    -- A subsingleton module has `⊤ = ⊥`, and `⊥` is finitely generated.
    have htop : (⊤ : Submodule ℂ (HolomorphicOneForm ℂ (OnePoint ℂ))) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x _
      exact Subsingleton.elim x 0
    rw [htop]
    exact Submodule.fg_bot

/--
The analytic genus of `OnePoint ℂ` (= ℂℙ¹) is zero.

Pure corollary of `holomorphicOneForm_onePointCx_subsingleton` via
`analyticGenus_eq_zero_of_subsingleton`.
-/
theorem analyticGenus_onePointCx_eq_zero :
    analyticGenus ℂ (OnePoint ℂ) = 0 := by
  haveI : Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ)) :=
    holomorphicOneForm_onePointCx_subsingleton
  exact analyticGenus_eq_zero_of_subsingleton

/-!
### TOPDOWN decomposition of `holomorphicOneFormLinearEquivOfHomeoSphere`
(integrated from Aristotle 88effa1c)

Reduced to a single sub-obligation
`subsingleton_holomorphicOneForm_of_homeo_sphere`. The linear
equivalence is then constructed via `LinearEquiv.ofSubsingleton`,
using the existing `holomorphicOneForm_onePointCx_subsingleton` for
the codomain.

The sub-obligation is now proved — see `subsingleton_holomorphicOneForm_of_homeo_sphere`
below — and *not* by the uniformization route sketched here: it goes through
`Periods.holomorphicOneForm_eq_zero_of_homeomorph_sphere` (simple connectivity
of the punctured sphere plus the covering space of primitives). Mathlib still
has none of uniformization at genus 0, pullback of holomorphic 1-forms along
biholomorphisms, or a simply-connected instance for `Metric.sphere` /
`OnePoint ℂ`; none of them is needed.
-/

/--
**Sub-obligation (uniformization-lite core), as originally planned.** A compact
connected Riemann surface homeomorphic to S² has a subsingleton space of
holomorphic 1-forms.

The plan recorded here was the deep route: the homeomorphism to S² combined
with uniqueness of complex structure on S² (uniformization at genus 0) implies
X is biholomorphic to `OnePoint ℂ ≃ ℂℙ¹`, which has `H⁰(Ω¹) = 0`. The
statement is proved below without uniformization; this structure survives only
as a carrier for the conclusion.
-/
structure HomeoSphereHolomorphicOneFormVanishing
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  subsingleton : Subsingleton (HolomorphicOneForm ℂ X)

/-!
### Structural companions for the uniformization-lite core

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`§Uniformization-lite`.
-/

/--
One source patch in the global genus-zero gluing construction.

This is intentionally a global-gluing object, not another local analytic leaf:
the coordinate function is attached to an open subset of `X`, and the target
chart is one of the two public charts on `OnePoint ℂ`.
-/
structure GenusZeroGlobalGluingPatch
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  source : Set X
  isOpen_source : IsOpen source
  targetChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ
  targetChart_standard : targetChart = identityChart ∨ targetChart = inversionChart
  coord : X → ℂ
  invCoord : ℂ → X
  coord_contMDiffOn :
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) coord source

/--
Global gluing data for the genus-zero uniformization step.

The fields are the chart-level obligations of the global-gluing plan: finite
source patches, target atlas choices, overlap compatibility of the local
coordinate limits, local inverse branches, and the resulting global
map/inverse with smoothness.  This is
strictly narrower than `exists_contMDiff_homeomorph_to_onePointCx`: it exposes
the chart-level obligations that the global construction must prove instead of
postulating a smooth homeomorphism directly.
-/
structure GenusZeroGlobalGluingData
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  PatchIndex : Type
  patch_fintype : Fintype PatchIndex
  patch_nonempty : Nonempty PatchIndex
  patch : PatchIndex → GenusZeroGlobalGluingPatch X
  patch_cover : ∀ x : X, ∃ i : PatchIndex, x ∈ (patch i).source
  target_chart_cover :
    ∀ y : OnePoint ℂ, ∃ (i : PatchIndex) (z : ℂ),
      z ∈ (patch i).targetChart.target ∧ y = (patch i).targetChart.symm z
  toMap : X → OnePoint ℂ
  invMap : OnePoint ℂ → X
  target_mem_on_patch :
    ∀ i x, x ∈ (patch i).source → toMap x ∈ (patch i).targetChart.source
  chart_expression_on_patch :
    ∀ i x, x ∈ (patch i).source →
      (patch i).targetChart (toMap x) = (patch i).coord x
  overlap_compatible :
    ∀ i j x,
      x ∈ (patch i).source → x ∈ (patch j).source →
        (patch i).targetChart.symm ((patch i).coord x) =
          (patch j).targetChart.symm ((patch j).coord x)
  inverse_branch_agrees_on_patch :
    ∀ i z, z ∈ (patch i).targetChart.target →
      invMap ((patch i).targetChart.symm z) = (patch i).invCoord z
  local_left_inverse_on_patch :
    ∀ i x, x ∈ (patch i).source → invMap (toMap x) = x
  local_right_inverse_on_target_chart :
    ∀ i z, z ∈ (patch i).targetChart.target →
      toMap ((patch i).invCoord z) = (patch i).targetChart.symm z
  contMDiff_toMap :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) toMap
  contMDiff_invMap :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) invMap

/--
The finite family of source patches and target-chart choices used before the
actual global map is assembled.
-/
structure GenusZeroGlobalPatchFamily
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  PatchIndex : Type
  patch_fintype : Fintype PatchIndex
  patch_nonempty : Nonempty PatchIndex
  patch : PatchIndex → GenusZeroGlobalGluingPatch X
  patch_cover : ∀ x : X, ∃ i : PatchIndex, x ∈ (patch i).source
  target_chart_cover :
    ∀ y : OnePoint ℂ, ∃ (i : PatchIndex) (z : ℂ),
      z ∈ (patch i).targetChart.target ∧ y = (patch i).targetChart.symm z

/--
Analytic patch-selection provider for the genus-zero global gluing step.

This is the narrow uniformization input the patch-family obligations were
cut against: a finite family of normalized Montel-limit coordinate patches,
tied to the chosen global map by the public `OnePoint ℂ` target charts.  The
root patch-family theorem below only forgets these analytic witnesses.

Nothing in the tree constructs this selector, and nothing outside this file
uses it: the genus-zero classification is proved by the route in
`genus_zero_homeomorph_onePointCx` / `analyticGenus_eq_zero_of_homeomorphic_sphere`
below, so this global-gluing section is retained plan scaffolding only. The
lemmas in it that take a selector as a hypothesis are all proved.
-/
structure GenusZeroNormalizedMontelPatchSelector
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  uniformization : X ≃ₜ OnePoint ℂ
  family : GenusZeroGlobalPatchFamily X
  coord_represents_uniformization :
    ∀ i x, x ∈ (family.patch i).source →
      (family.patch i).targetChart.symm ((family.patch i).coord x) =
        uniformization x
  invCoord_represents_uniformization :
    ∀ i z, z ∈ (family.patch i).targetChart.target →
      (family.patch i).invCoord z =
        uniformization.symm ((family.patch i).targetChart.symm z)
  uniformization_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) (uniformization : X → OnePoint ℂ)
  inverse_uniformization_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) (uniformization.symm : OnePoint ℂ → X)

/--
The genuine genus-zero uniformization provider: construct a biholomorphic
homeomorphism to `OnePoint ℂ`.  The patch selector below is then an explicit
two-chart packaging of this map.
-/
structure GenusZeroSmoothUniformization
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  uniformization : X ≃ₜ OnePoint ℂ
  contMDiff_uniformization :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) (uniformization : X → OnePoint ℂ)
  contMDiff_symm :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) (uniformization.symm : OnePoint ℂ → X)


/--
Degree-one meromorphic route data strong enough to give the smooth
uniformization used by the global-gluing selector.

This is narrower than a bare `GenusZeroSmoothUniformization`: it records that
the forward map comes from a degree-one meromorphic map to the Riemann sphere.
The inverse topology and smoothness are derived below from compactness,
bijectivity, and local branch-cover inverse holomorphicity.
-/
structure GenusZeroDegreeOneBiholomorphicRoute
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  meromorphicMap : MeromorphicMapToSphere X
  analyticData : meromorphicMap.AnalyticData
  branchedCoverData : BranchedCoverData X (OnePoint ℂ) meromorphicMap.toMap
  ramificationIndex_compatible :
    branchedCoverData.RamificationIndexCompatible
  branchedDegree_one : branchedDegree branchedCoverData = 1

/--
Single-pole meromorphic route data for the degree-one parametrization.

This is the next smaller analytic payload: a nonconstant meromorphic map to
the Riemann sphere with explicit analytic data and exactly one simple pole.
The compatible degree-one branched-cover package is derived from this data.
-/
structure GenusZeroSinglePoleMeromorphicRoute
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  meromorphicMap : MeromorphicMapToSphere X
  pole : X
  poleDivisor_eq : meromorphicMap.poles = Divisor.point pole
  nonconstant : meromorphicMap.Nonconstant
  analyticData : meromorphicMap.AnalyticData

/--
Existing single-pole analytic data directly gives the single-pole route
payload used by the genus-zero classification assembly.
-/
noncomputable def SinglePoleMeromorphicAnalyticData.toGenusZeroSinglePoleMeromorphicRoute
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {P : X} (data : SinglePoleMeromorphicAnalyticData (X := X) P) :
    GenusZeroSinglePoleMeromorphicRoute X where
  meromorphicMap := data.map
  pole := P
  poleDivisor_eq := data.poleDivisor_eq
  nonconstant := data.nonconstant
  analyticData := data.analyticData

/--
A degree-one branched cover is unramified at every source point. This is the
local inverse gateway for the biholomorphic inverse-smoothness step.
-/
theorem BranchedCoverData.ramificationIndex_eq_one_of_branchedDegree_one
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f)
    (hdeg : branchedDegree h = 1) (x : X) :
    h.ramificationIndex x = 1 := by
  classical
  obtain ⟨x₀, hfiber, hram⟩ := branchedDegree_one_fiber_singleton h (f x) hdeg
  have hxmem : x ∈ (h.finite_fiber (f x)).toFinset := by
    rw [Set.Finite.mem_toFinset]
    rfl
  rw [hfiber, Finset.mem_singleton] at hxmem
  rw [hxmem]
  exact hram

namespace GenusZeroDegreeOneBiholomorphicRoute

/-- The branch-cover part of a degree-one route is unramified everywhere. -/
theorem ramificationIndex_eq_one
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (route : GenusZeroDegreeOneBiholomorphicRoute X) (x : X) :
    route.branchedCoverData.ramificationIndex x = 1 :=
  route.branchedCoverData.ramificationIndex_eq_one_of_branchedDegree_one
    route.branchedDegree_one x

/--
At every point of a degree-one route, the branch-cover local inverse is a
two-sided inverse on open neighborhoods.
-/
theorem localInverse_is_inverse
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (route : GenusZeroDegreeOneBiholomorphicRoute X) (x : X) :
    ∃ U : Set X, ∃ V : Set (OnePoint ℂ),
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ route.meromorphicMap.toMap x ∈ V ∧
      Set.BijOn route.meromorphicMap.toMap U V ∧
      (∀ y' ∈ V,
        route.meromorphicMap.toMap
            (route.branchedCoverData.localInverseAt x
              (route.ramificationIndex_eq_one x) y') = y') ∧
      (∀ x' ∈ U,
        route.branchedCoverData.localInverseAt x
            (route.ramificationIndex_eq_one x)
            (route.meromorphicMap.toMap x') = x') :=
  route.branchedCoverData.localInverse_is_inverse
    (route.ramificationIndex_eq_one x)


/--
The inverse of the degree-one bijection agrees near every target point with
the branch-cover local inverse at the corresponding source point.
-/
theorem eventuallyEq_symm_localInverseAt
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (route : GenusZeroDegreeOneBiholomorphicRoute X) (y : OnePoint ℂ) :
    let e : X ≃ OnePoint ℂ :=
      Equiv.ofBijective route.meromorphicMap.toMap
        (degree_one_bijective route.branchedCoverData route.branchedDegree_one)
    (e.symm : OnePoint ℂ → X) =ᶠ[𝓝 y]
      route.branchedCoverData.localInverseAt (e.symm y)
        (route.ramificationIndex_eq_one (e.symm y)) := by
  classical
  intro e
  obtain ⟨_U, V, _hUopen, hVopen, _hxU, hfxV, _hbij, hright, _hleft⟩ :=
    route.localInverse_is_inverse (e.symm y)
  have hey : route.meromorphicMap.toMap (e.symm y) = y := e.apply_symm_apply y
  have hyV : y ∈ V := by
    simpa [hey] using hfxV
  filter_upwards [hVopen.mem_nhds hyV] with y' hy'V
  apply e.injective
  simp [e, hright y' hy'V]


/--
The inverse of the degree-one bijection is continuous, derived from the
continuous forward meromorphic map and compact-to-T2 bijectivity.
-/
theorem continuous_invMap
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (route : GenusZeroDegreeOneBiholomorphicRoute X) :
    Continuous
        ((Equiv.ofBijective route.meromorphicMap.toMap
          (degree_one_bijective route.branchedCoverData route.branchedDegree_one)).symm :
            OnePoint ℂ → X) := by
  classical
  let e : X ≃ OnePoint ℂ :=
    Equiv.ofBijective route.meromorphicMap.toMap
      (degree_one_bijective route.branchedCoverData route.branchedDegree_one)
  have he : Continuous e := by
    simpa [e] using route.analyticData.continuous_toMap
  simpa [e] using he.continuous_symm_of_equiv_compact_to_t2


end GenusZeroDegreeOneBiholomorphicRoute


namespace GenusZeroGlobalGluingData

/-- The homeomorphism obtained after the global gluing data is complete. -/
noncomputable def toHomeomorph
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (data : GenusZeroGlobalGluingData X) :
    X ≃ₜ OnePoint ℂ where
  toFun := data.toMap
  invFun := data.invMap
  left_inv := by
    intro x
    rcases data.patch_cover x with ⟨i, hx⟩
    exact data.local_left_inverse_on_patch i x hx
  right_inv := by
    intro y
    rcases data.target_chart_cover y with ⟨i, z, hz, rfl⟩
    rw [data.inverse_branch_agrees_on_patch i z hz]
    exact data.local_right_inverse_on_target_chart i z hz
  continuous_toFun := data.contMDiff_toMap.continuous
  continuous_invFun := data.contMDiff_invMap.continuous

/--
Completed global gluing data gives exactly the smooth homeomorphism required by
the genus-zero uniformization target.
-/
theorem exists_contMDiff_homeomorph
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (data : GenusZeroGlobalGluingData X) :
    ∃ (f : X ≃ₜ OnePoint ℂ),
      ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) f ∧
      ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) f.symm := by
  refine ⟨data.toHomeomorph, ?_, ?_⟩
  · exact data.contMDiff_toMap
  · exact data.contMDiff_invMap

end GenusZeroGlobalGluingData

/-
Early form-transport helper used by the top-down genus-zero route.  This is
the same pullback construction as the later public
`pullbackLinearEquivOfHomeomorph`, placed here so the current root can assemble
before the downstream global-gluing section.
-/
noncomputable def holomorphicOneFormLinearEquivOfContMDiffHomeomorph
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    (e : X ≃ₜ Y)
    (he : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤ e)
    (he_symm : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤ e.symm) :
    HolomorphicOneForm ℂ X ≃ₗ[ℂ] HolomorphicOneForm ℂ Y := by
  refine LinearEquiv.ofLinear
    (pullbackFormsBundledLM Y X e.symm he_symm)
    (pullbackFormsBundledLM X Y e he) ?_ ?_
  · convert rfl
    convert pullbackFormsBundledLM_comp _ _ _ _ using 1
    convert pullbackFormsBundledLM_id.symm
    exact funext fun x => e.apply_symm_apply x
  · convert rfl
    convert pullbackFormsBundledLM_comp _ _ _ _ using 1
    convert pullbackFormsBundledLM_id.symm
    exact funext fun x => e.symm_apply_apply x


/--
Target-membership step for local gluing coordinates (proved): every normalized
local coordinate value actually lies in the target of the patch's assigned
`OnePoint ℂ` chart.
-/
theorem genusZeroGlobalGluing_coord_mem_target_on_patch
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (family : GenusZeroGlobalPatchFamily X) :
    ∀ i x, x ∈ (family.patch i).source →
      (family.patch i).coord x ∈ (family.patch i).targetChart.target := by
  intro i x _hx
  rcases (family.patch i).targetChart_standard with hchart | hchart
  · rw [hchart]
    simp [identityChart, Topology.IsOpenEmbedding.toOpenPartialHomeomorph]
  · rw [hchart]
    simp [inversionChart]

/--
The canonical forward candidate obtained by choosing one patch containing each
point and evaluating that patch's target-chart inverse on its local coordinate.
-/
noncomputable def genusZeroGlobalGluing_toMap
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (family : GenusZeroGlobalPatchFamily X) : X → OnePoint ℂ :=
  fun x =>
    let i := Classical.choose (family.patch_cover x)
    (family.patch i).targetChart.symm ((family.patch i).coord x)

/--
The chosen-patch formula agrees with the global uniformization represented by
the normalized Montel patch selector.
-/
theorem genusZeroGlobalGluing_toMap_eq_uniformization
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ∀ x, genusZeroGlobalGluing_toMap selector.family x = selector.uniformization x := by
  intro x
  classical
  let i : selector.family.PatchIndex := Classical.choose (selector.family.patch_cover x)
  have hi : x ∈ (selector.family.patch i).source :=
    Classical.choose_spec (selector.family.patch_cover x)
  simpa [genusZeroGlobalGluing_toMap, i] using
    selector.coord_represents_uniformization i x hi

/--
Overlap-compatibility step (proved) through the public `OnePoint ℂ` transition
charts.
-/
theorem genusZeroGlobalGluing_overlap_compatible
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ∀ i j x,
      x ∈ (selector.family.patch i).source → x ∈ (selector.family.patch j).source →
        (selector.family.patch i).targetChart.symm ((selector.family.patch i).coord x) =
          (selector.family.patch j).targetChart.symm ((selector.family.patch j).coord x) := by
  intro i j x hi hj
  exact (selector.coord_represents_uniformization i x hi).trans
    (selector.coord_represents_uniformization j x hj).symm

/--
The canonical glued map lands in every target chart on the corresponding
source patch.
-/
theorem genusZeroGlobalGluing_toMap_target_mem_on_patch
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ∀ i x, x ∈ (selector.family.patch i).source →
      genusZeroGlobalGluing_toMap selector.family x ∈
        (selector.family.patch i).targetChart.source := by
  intro i x hx
  have hcoord_i :
      (selector.family.patch i).coord x ∈ (selector.family.patch i).targetChart.target :=
    genusZeroGlobalGluing_coord_mem_target_on_patch selector.family i x hx
  have hmem :
      (selector.family.patch i).targetChart.symm ((selector.family.patch i).coord x) ∈
        (selector.family.patch i).targetChart.source :=
    (selector.family.patch i).targetChart.map_target hcoord_i
  have hto :
      genusZeroGlobalGluing_toMap selector.family x = selector.uniformization x :=
    genusZeroGlobalGluing_toMap_eq_uniformization selector x
  have hrep :
      (selector.family.patch i).targetChart.symm ((selector.family.patch i).coord x) =
        selector.uniformization x :=
    selector.coord_represents_uniformization i x hx
  rw [hto, ← hrep]
  exact hmem

/--
Global candidate-map construction: the chosen-patch formula gives a single
candidate `X → OnePoint ℂ` landing in the selected target chart on every patch.
-/
theorem genusZeroGlobalGluing_toMap_exists
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ∃ toMap : X → OnePoint ℂ,
      ∀ i x, x ∈ (selector.family.patch i).source →
        toMap x ∈ (selector.family.patch i).targetChart.source := by
  exact ⟨genusZeroGlobalGluing_toMap selector.family,
    genusZeroGlobalGluing_toMap_target_mem_on_patch selector⟩

/--
Chart expression for the canonical glued global map.
-/
theorem genusZeroGlobalGluing_chart_expression_on_patch
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ∀ i x, x ∈ (selector.family.patch i).source →
      (selector.family.patch i).targetChart (genusZeroGlobalGluing_toMap selector.family x) =
        (selector.family.patch i).coord x := by
  intro i x hx
  have hcoord_i :
      (selector.family.patch i).coord x ∈ (selector.family.patch i).targetChart.target :=
    genusZeroGlobalGluing_coord_mem_target_on_patch selector.family i x hx
  have hto :
      genusZeroGlobalGluing_toMap selector.family x = selector.uniformization x :=
    genusZeroGlobalGluing_toMap_eq_uniformization selector x
  have hrep :
      (selector.family.patch i).targetChart.symm ((selector.family.patch i).coord x) =
        selector.uniformization x :=
    selector.coord_represents_uniformization i x hx
  rw [hto, ← hrep]
  exact (selector.family.patch i).targetChart.right_inv hcoord_i

/--
Inverse-candidate construction step (proved) from the local inverse branches.
-/
theorem genusZeroGlobalGluing_invMap_exists
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ∃ invMap : OnePoint ℂ → X,
      ∀ i z, z ∈ (selector.family.patch i).targetChart.target →
        invMap ((selector.family.patch i).targetChart.symm z) =
          (selector.family.patch i).invCoord z := by
  refine ⟨selector.uniformization.symm, ?_⟩
  intro i z hz
  exact (selector.invCoord_represents_uniformization i z hz).symm

/--
Local left-inverse step (proved) for the glued candidate maps.
-/
theorem genusZeroGlobalGluing_local_left_inverse_on_patch
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ∀ i x, x ∈ (selector.family.patch i).source →
      selector.uniformization.symm (genusZeroGlobalGluing_toMap selector.family x) = x := by
  intro _i x _hx
  rw [genusZeroGlobalGluing_toMap_eq_uniformization selector x]
  exact selector.uniformization.left_inv x

/--
Local right-inverse step (proved) for target-chart inverse branches.
-/
theorem genusZeroGlobalGluing_local_right_inverse_on_target_chart
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ∀ i z, z ∈ (selector.family.patch i).targetChart.target →
      genusZeroGlobalGluing_toMap selector.family ((selector.family.patch i).invCoord z) =
        (selector.family.patch i).targetChart.symm z := by
  intro i z hz
  rw [genusZeroGlobalGluing_toMap_eq_uniformization selector]
  rw [selector.invCoord_represents_uniformization i z hz]
  exact selector.uniformization.right_inv ((selector.family.patch i).targetChart.symm z)

/--
Local-chart smoothness step (proved) for the glued global map.
-/
theorem genusZeroGlobalGluing_contMDiff_toMap
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) (genusZeroGlobalGluing_toMap selector.family) := by
  have hfun :
      genusZeroGlobalGluing_toMap selector.family =
        (selector.uniformization : X → OnePoint ℂ) := by
    funext x
    exact genusZeroGlobalGluing_toMap_eq_uniformization selector x
  rw [hfun]
  exact selector.uniformization_contMDiff

/--
Local-chart smoothness step (proved) for the glued inverse map.
-/
theorem genusZeroGlobalGluing_contMDiff_invMap
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) (selector.uniformization.symm : OnePoint ℂ → X) := by
  exact selector.inverse_uniformization_contMDiff


/-
Construct a `ℂ`-linear equivalence between holomorphic 1-form spaces
from a smooth homeomorphism and its smooth inverse, using functorial
pullback. The pullback along `e` and `e.symm` give inverse linear maps
by composition and identity functoriality.
-/
noncomputable def pullbackLinearEquivOfHomeomorph
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    (e : X ≃ₜ Y)
    (he : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤ e)
    (he_symm : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤ e.symm) :
    HolomorphicOneForm ℂ X ≃ₗ[ℂ] HolomorphicOneForm ℂ Y := by
  refine LinearEquiv.ofLinear
    (pullbackFormsBundledLM Y X e.symm he_symm)
    (pullbackFormsBundledLM X Y e he) ?_ ?_
  · -- (pullback e) ∘ (pullback e.symm) = id on forms of X
    convert rfl;
    convert pullbackFormsBundledLM_comp _ _ _ _ using 1;
    convert pullbackFormsBundledLM_id.symm;
    exact funext fun x => e.apply_symm_apply x
  · -- (pullback e.symm) ∘ (pullback e) = id on forms of Y
    convert rfl;
    convert pullbackFormsBundledLM_comp _ _ _ _ using 1;
    convert pullbackFormsBundledLM_id.symm;
    exact funext fun x => e.symm_apply_apply x

theorem holomorphicOneForm_linearEquiv_of_biholo_to_OnePointCx
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (_e : X ≃ₜ OnePoint ℂ) :
    Nonempty (HolomorphicOneForm ℂ X ≃ₗ[ℂ] HolomorphicOneForm ℂ (OnePoint ℂ)) := by
  -- Both spaces are zero: `X` is homeomorphic to `S²`
  -- (`Periods.holomorphicOneForm_eq_zero_of_homeomorph_sphere`).
  haveI : Subsingleton (HolomorphicOneForm ℂ X) := ⟨fun a b => by
    rw [JacobianChallenge.Periods.holomorphicOneForm_eq_zero_of_homeomorph_sphere a
        (_e.trans onePointCx_homeomorph_sphere),
      JacobianChallenge.Periods.holomorphicOneForm_eq_zero_of_homeomorph_sphere b
        (_e.trans onePointCx_homeomorph_sphere)]⟩
  haveI : Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ)) :=
    holomorphicOneForm_onePointCx_subsingleton
  exact ⟨LinearEquiv.ofSubsingleton _ _⟩


/--
A topological homeomorphism from a compact connected complex 1-manifold `X` to the standard
2-sphere gives a `ℂ`-linear isomorphism between the spaces of holomorphic 1-forms on `X` and
`OnePoint ℂ`: both are zero (`Periods.holomorphicOneForm_eq_zero_of_homeomorph_sphere`, via
simple connectivity of the punctured sphere; no uniformization).

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:holomorphic-one-form-equiv-of-homeo-sphere`.
-/
theorem holomorphicOneForm_linearEquiv_of_homeoSphere_exists
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    Nonempty (HolomorphicOneForm ℂ X ≃ₗ[ℂ] HolomorphicOneForm ℂ (OnePoint ℂ)) := by
  obtain ⟨e⟩ := h
  haveI : Subsingleton (HolomorphicOneForm ℂ X) := ⟨fun a b => by
    rw [JacobianChallenge.Periods.holomorphicOneForm_eq_zero_of_homeomorph_sphere a e,
      JacobianChallenge.Periods.holomorphicOneForm_eq_zero_of_homeomorph_sphere b e]⟩
  haveI : Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ)) :=
    holomorphicOneForm_onePointCx_subsingleton
  exact ⟨LinearEquiv.ofSubsingleton _ _⟩

/--
**Uniformization-lite core (proved).** A compact connected Riemann surface
homeomorphic to S² has no nonzero holomorphic 1-forms. Was an opaque data
obligation; it is now proved via
`holomorphicOneForm_linearEquiv_of_homeoSphere_exists`.
-/
theorem homeoSphereHolomorphicOneFormVanishing
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    Subsingleton (HolomorphicOneForm ℂ X) := by
  obtain ⟨e⟩ := holomorphicOneForm_linearEquiv_of_homeoSphere_exists X h
  haveI : Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ)) :=
    holomorphicOneForm_onePointCx_subsingleton
  exact e.toEquiv.subsingleton


theorem subsingleton_holomorphicOneForm_of_homeo_sphere
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    Subsingleton (HolomorphicOneForm ℂ X) := by
  exact homeoSphereHolomorphicOneFormVanishing X h

/--
**Bottom-up obligation (uniformization-lite).** A compact connected
Riemann surface `X` homeomorphic to the standard 2-sphere `S²` admits
a ℂ-linear equivalence between its space of holomorphic 1-forms and
that of `OnePoint ℂ`.
-/
noncomputable def holomorphicOneFormLinearEquivOfHomeoSphere
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (_h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    HolomorphicOneForm ℂ X ≃ₗ[ℂ] HolomorphicOneForm ℂ (OnePoint ℂ) := by
  haveI : Subsingleton (HolomorphicOneForm ℂ X) :=
    subsingleton_holomorphicOneForm_of_homeo_sphere X _h
  haveI : Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ)) :=
    holomorphicOneForm_onePointCx_subsingleton
  exact LinearEquiv.ofSubsingleton _ _

/--
Transport step: a compact Riemann surface `X` homeomorphic to the
standard 2-sphere has the same analytic genus as `OnePoint ℂ`.

This was planned as the "uniformization-lite" step (homeomorphism to `S²` plus
uniqueness of the complex structure on `S²` forces a biholomorphism
`X ≃ OnePoint ℂ`, which induces a ℂ-linear isomorphism of holomorphic 1-form
spaces). The proof actually used needs no uniformization: both form spaces are
subsingleton (`holomorphicOneFormLinearEquivOfHomeoSphere`, ultimately
`Periods.holomorphicOneForm_eq_zero_of_homeomorph_sphere`), so the ℂ-linear
equivalence is `LinearEquiv.ofSubsingleton` and the genera agree.

Stated as an equality of natural numbers, since both sides are defined
once their `FiniteDimensionalHolomorphicOneForms` instances are
available (`X`'s comes from the hypothesis, `OnePoint ℂ`'s comes from
`finiteDimensionalHolomorphicOneForms_onePointCx` above).
-/
theorem analyticGenus_eq_of_homeomorphic_sphere_of_onePointCx
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (_h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    analyticGenus ℂ X = analyticGenus ℂ (OnePoint ℂ) := by
  -- Decompose via a ℂ-linear equivalence of holomorphic 1-form spaces;
  -- `holomorphicOneFormLinearEquivOfHomeoSphere`.
  have e := holomorphicOneFormLinearEquivOfHomeoSphere X _h
  exact e.finrank_eq

/--
The "easy" direction: if `X` is homeomorphic to the standard 2-sphere
then `analyticGenus ℂ X = 0`.

Proved directly from `Periods.holomorphicOneForm_eq_zero_of_homeomorph_sphere`
(simple connectivity of the punctured sphere plus the covering space of
primitives) and `analyticGenus_eq_zero_iff_subsingleton` — see the proof below.

Two earlier routes to the same statement are still available in this file but
are not used here: composing
`analyticGenus_eq_of_homeomorphic_sphere_of_onePointCx` with
`analyticGenus_onePointCx_eq_zero`, and the uniformization argument (a compact
Riemann surface homeomorphic to `S²` has the complex structure of `ℂℙ¹`, whose
canonical sheaf has degree `-2 < 0`).
-/
theorem analyticGenus_eq_zero_of_homeomorphic_sphere
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    analyticGenus ℂ X = 0 := by
  -- A surface homeomorphic to `S²` carries no nonzero holomorphic 1-form
  -- (`Periods.holomorphicOneForm_eq_zero_of_homeomorph_sphere`: simple connectivity of the
  -- punctured sphere + the covering space of primitives). No uniformization needed.
  obtain ⟨e⟩ := h
  refine analyticGenus_eq_zero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
  rw [JacobianChallenge.Periods.holomorphicOneForm_eq_zero_of_homeomorph_sphere a e,
    JacobianChallenge.Periods.holomorphicOneForm_eq_zero_of_homeomorph_sphere b e]

/-!
#### Status of this note

Everything from here to the end of this comment block is a **historical
survey**, written when the hard direction was still open and against a
Mathlib v4.28.0 snapshot. The hard direction is now proved:
`genus_zero_homeomorph_onePointCx` (below) discharges it via
`JacobianChallenge.Surface.homeomorph_onePoint_of_forall_eq_zero`, and
`homeomorphic_sphere_of_analyticGenus_eq_zero` /
`analyticGenus_eq_zero_iff_homeomorphic_sphere` close the classification. The
`[MISSING ❌]` dependency graphs, the three-step plan and the "Honest
assessment" below describe routes that were *not* taken; they are kept only as
a record of the Mathlib survey. Do not read them as current status.

#### Mathematical content

A compact connected Riemann surface `X` with `analyticGenus ℂ X = 0`
(i.e. `H⁰(X, Ω¹) = 0`, equivalently
`Subsingleton (HolomorphicOneForm ℂ X)` by
`analyticGenus_eq_zero_iff_subsingleton`) is homeomorphic to `S²`.

The standard proof runs through the following chain:

1. **Genus 0 ⟹ simply connected.** By the topological classification
   of compact oriented surfaces, the topological genus equals the
   analytic genus (Hodge theory / de Rham). A compact oriented surface
   of topological genus 0 is simply connected.

2. **Simply connected compact Riemann surface ⟹ biholomorphic to ℂℙ¹.**
   The uniformization theorem says every simply connected Riemann surface
   is biholomorphic to ℂ, 𝔻, or ℂℙ¹. Compactness rules out ℂ and 𝔻.

3. **ℂℙ¹ ≃ₜ S².** The one-point compactification of ℂ (= ℂℙ¹ as a
   topological space) is homeomorphic to the standard 2-sphere in ℝ³
   via stereographic projection.

An alternative route avoids uniformization entirely by using Riemann–Roch
+ a rational function argument:

1'. **Genus 0 + Riemann–Roch ⟹ ∃ meromorphic function of degree 1.**
    With `g = 0`, Riemann–Roch gives `ℓ(D) - ℓ(K-D) ≥ deg D + 1` for
    any divisor `D`. Taking `D` = a single point gives a meromorphic
    function with a single simple pole, i.e. of degree 1.

2'. **Degree-1 meromorphic function ⟹ biholomorphism to ℂℙ¹.**
    A meromorphic function of degree 1 on a compact Riemann surface is a
    biholomorphism onto ℂℙ¹.

3'. Same as step 3.

#### Mathlib API survey

| Concept searched | Found? | Notes |
|---|---|---|
| `uniformization` | ❌ | No uniformization theorem in any form. |
| `RiemannSurface` | ❌ | No dedicated Riemann surface type. |
| `ComplexProjectiveLine` / `RiemannSphere` | ❌ | Not defined as a type or manifold. |
| `Projectivization` | ✅ | `Projectivization ℂ (Fin 2 → ℂ)` exists but has no manifold or complex-analytic structure. |
| `OnePoint` (one-point compactification) | ✅ | `OnePoint ℂ` exists, is `CompactSpace`, but has no `T2Space`, `ChartedSpace`, or `IsManifold` instance. No homeomorphism to `Metric.sphere`. |
| `stereographic` / `stereographic'` | ✅ | Stereographic projection exists for `Metric.sphere (0 : E) 1` in a real inner product space `E`. Gives `ChartedSpace (EuclideanSpace ℝ (Fin n))` and `IsManifold (𝓡 n)` for the `n`-sphere in `ℝⁿ⁺¹`. The 2-sphere is charted over `EuclideanSpace ℝ (Fin 2)`, **not** over `ℂ`. |
| `EuclideanSpace.instChartedSpaceSphere` | ✅ | Gives `ChartedSpace (EuclideanSpace ℝ (Fin 2))` on `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`. The model is *real*, not complex. |
| `IsManifold` for sphere | ✅ | `IsManifold (𝓡 2) ⊤` on `S²` exists (real smooth manifold). No complex manifold instance. |
| `SimplyConnectedSpace` | ✅ | Class exists. No instance for `S²` or `OnePoint ℂ`. |
| `IsCoveringMap` | ✅ | Covering map API exists with path-lifting. No universal covering construction for Riemann surfaces. |
| `MeromorphicAt` | ✅ | Pointwise meromorphic function API exists (orders, trailing coefficients). No global meromorphic function type on manifolds; no divisor theory. |
| `Divisor` / `RiemannRoch` | ❌ | No divisor theory, no Riemann–Roch theorem. |
| `Hodge` / `deRham` / `topologicalGenus` | ❌ | No Hodge theory, no de Rham cohomology, no topological genus. |
| `Homeomorph.compactificationToSphere` | ❌ | No homeomorphism `OnePoint ℂ ≃ₜ S²`. |
| `EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ` | Partial | `Complex.measurableEquiv` and `Complex.isometry_ofReal` exist but a full `LinearIsometryEquiv` from `EuclideanSpace ℝ (Fin 2)` to `ℂ` is not directly available as a named lemma. |

#### Dependency graph

```
homeomorphic_sphere_of_analyticGenus_eq_zero
  │
  ├─► analyticGenus_eq_zero_iff_subsingleton  [AVAILABLE ✅]
  │     (converts hypothesis to Subsingleton (HolomorphicOneForm ℂ X))
  │
  ├─► [MISSING ❌] genus_zero_implies_simply_connected
  │     ├─► [MISSING ❌] analytic_genus_eq_topological_genus (Hodge theory)
  │     │     ├─► [MISSING ❌] de Rham cohomology
  │     │     └─► [MISSING ❌] Hodge decomposition
  │     └─► [MISSING ❌] topological classification of compact oriented surfaces
  │           └─► [MISSING ❌] surface_genus_zero_iff_simply_connected
  │
  ├─► [MISSING ❌] uniformization_compact_simply_connected
  │     ├─► [MISSING ❌] uniformization_theorem
  │     │     ├─► [MISSING ❌] universal covering of Riemann surface
  │     │     ├─► [MISSING ❌] Riemann mapping theorem (for ℂ and 𝔻)
  │     │     └─► [MISSING ❌] Koebe's theorem / Perron's method
  │     └─► [MISSING ❌] compactness rules out ℂ and 𝔻
  │
  ├─► [MISSING ❌] CP1_def : ℂℙ¹ as a complex manifold
  │     ├─► [PARTIAL] Projectivization ℂ (Fin 2 → ℂ) (no manifold structure)
  │     └─► [PARTIAL] OnePoint ℂ (no T2, no manifold structure)
  │
  └─► [MISSING ❌] CP1_homeomorph_sphere : ℂℙ¹ ≃ₜ S²
        ├─► [PARTIAL] stereographic / stereographic' (real model only)
        └─► [MISSING ❌] OnePoint ℂ ≃ₜ Metric.sphere 0 1 in ℝ³
```

**Alternative route via Riemann–Roch:**

```
homeomorphic_sphere_of_analyticGenus_eq_zero
  │
  ├─► [AVAILABLE ✅] analyticGenus_eq_zero_iff_subsingleton
  │
  ├─► [MISSING ❌] riemann_roch_genus_zero_degree_one_function
  │     ├─► [MISSING ❌] Riemann–Roch theorem
  │     │     ├─► [MISSING ❌] sheaf cohomology on Riemann surfaces
  │     │     └─► [MISSING ❌] Serre duality
  │     └─► [MISSING ❌] divisor theory
  │
  ├─► [MISSING ❌] degree_one_meromorphic_iff_biholomorphic_CP1
  │     └─► [MISSING ❌] global meromorphic functions on manifolds
  │
  └─► [MISSING ❌] CP1_homeomorph_sphere (same as above)
```

#### 3-step Mathlib-API plan for a future job

**Step 1 — Build `ℂℙ¹` as a complex manifold and prove `ℂℙ¹ ≃ₜ S²`.**

Define `ℂℙ¹` as `OnePoint ℂ` (the Alexandrov one-point compactification
of `ℂ`). Equip it with:
- A `T2Space` instance (requires locally compact + T2 of `ℂ`, which
  Mathlib already has).
- A `ChartedSpace ℂ` instance via two charts: `z ↦ z` on `ℂ ⊂ OnePoint ℂ`
  and `z ↦ 1/z` on `(OnePoint ℂ) \ {0}`.
- An `IsManifold (modelWithCornersSelf ℂ ℂ) ⊤` instance by showing chart
  transitions are holomorphic (they are `z ↦ 1/z` on `ℂ \ {0}`).
- A `Homeomorph` from `OnePoint ℂ` to `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`
  by composing the identification `ℂ ≅ ℝ²` with the inverse of
  stereographic projection and extending continuously to the point at
  infinity.

**Estimated difficulty:** Medium-hard. The topological parts (compact,
connected, T2) are close to what Mathlib has for `OnePoint`. The main
work is constructing the complex atlas and proving the homeomorphism
with `S²`. The latter requires showing that `stereographic'⁻¹ ∘ (ℂ → ℝ²)`
extends continuously to a bijection `OnePoint ℂ → S²`. Roughly 300–600
lines of new Lean code.

**Step 2 — Prove `H⁰(ℂℙ¹, Ω¹) = 0` directly (no Riemann–Roch).**

Show `Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ))` by a direct
argument: a holomorphic 1-form on `OnePoint ℂ` restricts to `f(z) dz`
on the standard chart `ℂ`, where `f : ℂ → ℂ` is entire. On the chart at
infinity, the transition gives `f(z) dz = -f(1/w) / w² dw`, which must
be holomorphic at `w = 0`. By Liouville's theorem (available in Mathlib:
`Complex.liouville_theorem`), `f` is constant, and the holomorphicity
condition at infinity forces the constant to be zero.

**Estimated difficulty:** Medium. Liouville's theorem is available.
The main challenge is formalizing what "holomorphic 1-form on a charted
space" means in terms of the chart transition — this depends on the
project's `HolomorphicOneForm` API and may require additional interface
lemmas.

**Step 3 — The actual uniformization step (genus 0 ⟹ biholomorphic to ℂℙ¹).**

This is the hardest step and has two possible sub-approaches:

**(3a) Via uniformization theorem (very hard).** Prove the uniformization
theorem for compact Riemann surfaces: every simply connected Riemann
surface is biholomorphic to ℂ, 𝔻, or ℂℙ¹. This is a major theorem
requiring Perron's method, Dirichlet problem on Riemann surfaces,
normal families, and the Riemann mapping theorem. Estimated at 2000+
lines of new Lean code. Then show `genus 0 ⟹ simply connected`
(requires Hodge theory or classification of surfaces).

**(3b) Via Riemann–Roch (hard).** Prove the Riemann–Roch theorem for
compact Riemann surfaces. Then the argument is: genus 0 ⟹ degree-1
meromorphic function exists ⟹ biholomorphism to ℂℙ¹. This avoids
uniformization but requires sheaf cohomology, Serre duality, and
divisor theory. Estimated at 1500+ lines.

**(3c) Via direct Mittag-Leffler–style argument (moderately hard).**
Avoid both uniformization and full Riemann–Roch. Use the vanishing
of `H¹(X, 𝒪)` (which follows from `H⁰(X, Ω¹) = 0` by Serre duality —
but Serre duality itself is nontrivial). Then Mittag-Leffler–type
arguments produce a meromorphic function of degree 1. This still
requires substantial analytic machinery not in Mathlib.

#### Honest assessment (as written at the time — superseded)

The verdict recorded here was that the theorem is **not realistically
formalizable** against Mathlib v4.28.0 along any of the routes surveyed above.
That remains true of those routes, and it is no longer the project's status:
the theorem is proved below by the `∂̄`-solvability route in
`Jacobian/Surface/`, which needs neither uniformization nor Riemann–Roch nor
Hodge theory. The assessment below is kept verbatim.

The gap along the surveyed routes was enormous:

- **ℂℙ¹ as a complex manifold** does not exist. Building it (Step 1)
is a self-contained project of moderate size (~500 lines) and is the
only step that could plausibly be completed in a focused effort.

- **The uniformization theorem** (or any equivalent, such as
Riemann–Roch for Riemann surfaces) is entirely absent and represents
one of the deepest results in complex analysis / algebraic geometry.
No path through Mathlib's current API gets close.

- **The bridge from analytic genus to topological genus** (Hodge theory /
de Rham cohomology) is also absent. Without it, even the implication
"genus 0 ⟹ simply connected" cannot be stated.

- **Comparison with the easy direction:** the easy direction
(`analyticGenus_eq_zero_of_homeomorphic_sphere`) requires showing
`H⁰(ℂℙ¹, Ω¹) = 0`, which can be done with Steps 1–2 alone (no
uniformization). The hard direction additionally requires Step 3,
which is strictly more demanding.

#### Nearest Mathlib footholds (for future work)

- `OnePoint` (one-point compactification): good starting point for
  defining `ℂℙ¹` topologically.
- `stereographic` / `stereographic'` / `EuclideanSpace.instChartedSpaceSphere`:
  real manifold structure on `S²`, needed for Step 1's homeomorphism.
- `Complex.liouville_theorem`: Liouville's theorem for bounded entire
  functions, needed for Step 2.
- `MeromorphicAt`: pointwise meromorphic function API, useful building
  block for Steps 2–3.
- `SimplyConnectedSpace`: the class exists, though no instance for `S²`.
- `IsCoveringMap` + path lifting: covering space theory, relevant if
  pursuing uniformization via universal covers.
-/

/--
The Riemann-Roch output in genus zero: a meromorphic map to `OnePoint ℂ`
whose pole divisor is the point divisor `[pole]`.
-/
structure GenusZeroSimplePoleMeromorphicMap
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  meromorphicMap : MeromorphicMapToSphere X
  pole : X
  simple_pole_cert : meromorphicMap.poles = Divisor.point pole

namespace GenusZeroSimplePoleMeromorphicMap

/-- The underlying map to the Riemann sphere. -/
def toMap {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : GenusZeroSimplePoleMeromorphicMap X) : X → OnePoint ℂ :=
  f.meromorphicMap.toMap

end GenusZeroSimplePoleMeromorphicMap

/--
The fields are the topological consequences needed by the final assembly:
continuity and bijectivity. A future refinement should replace this bridge by
properness plus the local degree calculation, then derive these fields.
-/
structure GenusZeroProperDegreeOneMap
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  toMap : X → OnePoint ℂ
  continuous_toMap : Continuous toMap
  bijective_toMap : Function.Bijective toMap
  degree_one_data : ∃ f : MeromorphicMapToSphere X,
    toMap = f.toMap ∧ Nonempty (MeromorphicDegreeOneData X f)

/--
At the topological surface needed here, this is represented by the resulting
homeomorphism. Future work can strengthen the structure with a biholomorphism
type once the project has one.
-/
structure GenusZeroBiholomorphicParametrization
    (X : Type*) [TopologicalSpace X] where
  toHomeomorph : X ≃ₜ OnePoint ℂ

/-!
### TOPDOWN decomposition for `genus_zero_homeomorph_onePointCx`

1. `genus_zero_exists_simplePole_meromorphicMap` — from
   `analyticGenus = 0`, Riemann-Roch produces a meromorphic function with one
   simple pole.
2. `simplePole_meromorphicMap_proper_degreeOne` — compactness/properness and
   divisor-degree bookkeeping promote that function to a proper degree-one map
   to `OnePoint ℂ`.
3. `proper_degreeOne_meromorphicMap_biholomorphic` — a proper degree-one
   holomorphic map is a biholomorphic parametrization, hence a homeomorphism.

Leaves 2 and 3 exist and are proved, as `simplePole_meromorphicMap_proper_degreeOne`
and `proper_degreeOne_meromorphicMap_biholomorphic` below (each taking its
analytic input as an explicit hypothesis); leaf 1 was never declared under that
name. `genus_zero_homeomorph_onePointCx` below does not use any of them: it goes
through `JacobianChallenge.Surface.homeomorph_onePoint_of_forall_eq_zero`. This
decomposition is kept as the record of the Riemann–Roch route.
-/

/--
Fixed-pole Riemann-Roch output, now backed by the production
meromorphic/divisor substrate.
-/
abbrev GenusZeroRiemannRochFixedPoleData
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (h : analyticGenus ℂ X = 0) : Type _ :=
  GenusZeroFixedPoleMeromorphicData X P h









/--
**Properness/degree data existence leaf (proved).** A one-simple-pole map,
given pole-modulus and branched-cover data, has a proper degree-one
promotion.

This refined the old properness/degree opaque into a named existence
statement, which is now proved: continuity, bijectivity and the
divisor-degree computation all come from
`meromorphicDegreeOneData_of_poleDivisor_point`.
-/
theorem properDegreeOneMapOfSimplePole_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (_f : GenusZeroSimplePoleMeromorphicMap X)
    (hmod : _f.meromorphicMap.PoleModulusData)
    (hbranch : _f.meromorphicMap.BranchedCoverDataOfPoleDegree) :
    Nonempty (GenusZeroProperDegreeOneMap X) := by
  let hdegree :=
    meromorphicDegreeOneData_of_poleDivisor_point X _f.meromorphicMap _f.pole
      _f.simple_pole_cert hmod hbranch
  refine hdegree.elim ?_
  intro data
  exact ⟨
    { toMap := _f.meromorphicMap.toMap
      continuous_toMap := data.continuous_toMap
      bijective_toMap := data.bijective_toMap
      degree_one_data := ⟨_f.meromorphicMap, rfl, ⟨data⟩⟩ }⟩

/--
**Properness/degree data assembly.** Extracts the degree-one promotion
from the named existence leaf.
-/
noncomputable def properDegreeOneMapOfSimplePole
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (f : GenusZeroSimplePoleMeromorphicMap X)
    (hmod : f.meromorphicMap.PoleModulusData)
    (hbranch : f.meromorphicMap.BranchedCoverDataOfPoleDegree) :
    GenusZeroProperDegreeOneMap X :=
  Classical.choice (properDegreeOneMapOfSimplePole_nonempty X f hmod hbranch)


theorem simplePole_meromorphicMap_proper_degreeOne
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (f : GenusZeroSimplePoleMeromorphicMap X)
    (hmod : f.meromorphicMap.PoleModulusData)
    (hbranch : f.meromorphicMap.BranchedCoverDataOfPoleDegree) :
    Nonempty (GenusZeroProperDegreeOneMap X) := by
  exact ⟨properDegreeOneMapOfSimplePole X f hmod hbranch⟩

/--
**Sub-obligation 3 (degree one implies parametrization) — proved.** A proper
degree-one meromorphic map from a compact connected Riemann surface to
`OnePoint ℂ` is a biholomorphic parametrization.

Proof below: the recorded continuity and bijectivity give a continuous
bijection from a compact space to a T₂ space, which
`Continuous.homeoOfEquivCompactToT2` promotes to the homeomorphism that
`GenusZeroBiholomorphicParametrization` records.
-/
theorem proper_degreeOne_meromorphicMap_biholomorphic
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (f : GenusZeroProperDegreeOneMap X) :
    Nonempty (GenusZeroBiholomorphicParametrization X) := by
  let e : X ≃ OnePoint ℂ := Equiv.ofBijective f.toMap f.bijective_toMap
  have he : Continuous e := by
    simpa [e] using f.continuous_toMap
  exact ⟨⟨he.homeoOfEquivCompactToT2⟩⟩




/--
**Uniformization (genus zero):** a compact connected Riemann surface
with `analyticGenus = 0` is homeomorphic to the one-point
compactification of `ℂ`.

1. Genus zero means every holomorphic 1-form vanishes, so the Hodge decomposition makes
   every smooth `(0,1)`-form `∂̄`-exact.
2. Solving `∂̄u = ∂̄(χ/(w - z₀))` gives a function with a single simple pole at a chosen point.
3. Its extension to `ℂ̂` is holomorphic of degree one, hence a homeomorphism
   (`JacobianChallenge.Surface.homeomorph_onePoint_of_forall_eq_zero`).
-/
theorem genus_zero_homeomorph_onePointCx
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (h : analyticGenus ℂ X = 0) :
    Nonempty (X ≃ₜ OnePoint ℂ) := by
  -- Genus zero: every holomorphic 1-form vanishes, so `∂̄` is solvable and there is a function
  -- with a single simple pole; it is a degree-one holomorphic map to `ℂ̂`
  -- (`JacobianChallenge.Surface.homeomorph_onePoint_of_forall_eq_zero`).
  haveI := analyticGenus_eq_zero_iff_subsingleton.mp h
  exact JacobianChallenge.Surface.homeomorph_onePoint_of_forall_eq_zero
    (fun η => Subsingleton.elim η 0)




theorem homeomorphic_sphere_of_analyticGenus_eq_zero
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (_h : analyticGenus ℂ X = 0) :
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  let ⟨e⟩ := genus_zero_homeomorph_onePointCx X _h
  ⟨e.trans onePointCx_homeomorph_sphere⟩


/--
A compact connected Riemann surface has analytic genus zero iff it is
homeomorphic to the standard 2-sphere.
-/
theorem analyticGenus_eq_zero_iff_homeomorphic_sphere
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    analyticGenus ℂ X = 0 ↔
      Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  ⟨homeomorphic_sphere_of_analyticGenus_eq_zero X,
   analyticGenus_eq_zero_of_homeomorphic_sphere X⟩

end JacobianChallenge.HolomorphicForms
