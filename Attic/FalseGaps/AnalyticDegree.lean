/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/TraceDegree/AnalyticDegree.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

/--
**The narrow push-pull descent provider.** The basis-aligned
Jacobian push-pull identity, descended from the trace-pullback
identity on holomorphic 1-forms through the period quotient.

### Status (post-rewire)
-/
noncomputable def analyticPushPull_provider (f : X → Y)
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (Q : BasisAnalyticJacobian Y) :
    analyticPushforward f hf (analyticPullback f hf Q) =
      (analyticDegree f hf) • Q := by
  -- Lift Q = mk v.
  obtain ⟨v, rfl⟩ :=
    ComplexTorus.mk_surjective _ (periodFullComplexLattice Y) Q
  -- Descend the pullback: analyticPullback (mk v) = mk (basisDualPullback f hf v).
  have hpull :
      analyticPullback f hf
        (ComplexTorus.mk _ (periodFullComplexLattice Y) v) =
      ComplexTorus.mk _ (periodFullComplexLattice X)
        ((traceDualPullbackLift f hf).toAddMonoidHom v) := by
    -- Both equal `mapClm traceDualPullbackLiftCLM _ (mk v)` definitionally.
    rfl
  rw [hpull]
  -- Descend the pushforward.
  rw [analyticPushforward_mk_spec_raw f hf
    ((traceDualPullbackLift f hf).toAddMonoidHom v)]
  -- Vector-level identity:
  -- pushforwardTraceLift ((traceDualPullbackLift) v) = (deg : ℂ) • v.
  have hvec :
      pushforwardTraceLift f hf
        ((traceDualPullbackLift f hf).toAddMonoidHom v) =
      (analyticDegree f hf : ℂ) • v := by
    have h := pushforwardTraceLift_traceDualPullbackLift_eq_degree_smul f hf
    have happ := DFunLike.congr_fun h v
    simpa only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq] using happ
  rw [hvec]
  -- mk ((n : ℂ) • v) = mk (n • v) = n • mk v.
  rw [Nat.cast_smul_eq_nsmul ℂ (analyticDegree f hf) v]
  exact ComplexTorus.mk_nsmul _ (analyticDegree f hf) v

/--
Bundled analytic trace/degree contract for a holomorphic map of compact
Riemann surfaces.

The fields are the mathematical laws needed by the public route theorems:
constant maps have degree zero (now a definitional fact), nonconstant
analytic degree agrees with the branched-cover degree of any compatible
witness (canonical theorem), the global trace agrees with the local
regular-fiber trace, trace after pullback is degree multiplication on
holomorphic forms, and the descended basis-aligned Jacobian maps satisfy
the corresponding push-pull identity.
-/
structure AnalyticTraceDegreeSpec (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) where
  /-- Constant maps have analytic degree zero. -/
  degree_constant : (∃ y₀, ∀ x, f x = y₀) → analyticDegree f hf = 0
  /--
For nonconstant maps, analytic degree agrees with the constructed
  branched-cover degree under the standard local ramification and weighted
  fiber conservation hypotheses.
-/
  degree_eq_branched :
    ∀ (hkfold : HasLocalKfoldRamification f) (hw : HasWeightedFiberConservation f)
      (hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀),
      analyticDegree f hf =
        branchedDegree
          (JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
            (isHolomorphic_of_contMDiff hf hkfold) hw hnonconst)
  /-- The global trace form agrees with the regular-value local trace. -/
  trace_regular : TraceFormsRegularSpec f hf
  /-- Form-level trace-pullback identity. -/
  trace_pullback :
    ∀ η : HolomorphicOneForm ℂ Y,
      traceFormsBundled f hf (pullbackFormsBundled f hf η) =
        (analyticDegree f hf : ℂ) • η
  /-- Basis-aligned Jacobian push-pull identity. -/
  push_pull :
    ∀ [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
      (Q : BasisAnalyticJacobian Y),
      analyticPushforward f hf (analyticPullback f hf Q) =
        (analyticDegree f hf) • Q

noncomputable def analyticTraceDegreeSpec_frontier (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    AnalyticTraceDegreeSpec f hf where
  degree_constant := analyticDegree_constant f hf
  degree_eq_branched := by
    intro hkfold hw hnonconst
    set hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
      (isHolomorphic_of_contMDiff hf hkfold) hw hnonconst with hbc_def
    have hcompat : hbc.RamificationIndexCompatible :=
      JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
        (isHolomorphic_of_contMDiff hf hkfold) hw hnonconst
    exact analyticDegree_eq_canonical_branchedDegree f hf
      (isHolomorphic_of_contMDiff hf hkfold) hbc hcompat hnonconst
  trace_regular := traceFormsRegularSpec_provider f hf
  trace_pullback := trace_pullback_provider f hf
  push_pull := fun Q => analyticPushPull_provider f hf Q

theorem analyticPushforward_analyticPullback_spec (f : X → Y)
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (Q : BasisAnalyticJacobian Y) :
    analyticPushforward f hf (analyticPullback f hf Q) =
      (analyticDegree f hf) • Q :=
  analyticPushPull_provider f hf Q

lemma analyticPushforward_analyticPullback (f : X → Y)
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (Q : BasisAnalyticJacobian Y) :
    analyticPushforward f hf (analyticPullback f hf Q) =
      (analyticDegree f hf) • Q :=
  analyticPushforward_analyticPullback_spec f hf Q
