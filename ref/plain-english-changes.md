# Plain-English changes log

Every plain-English block (blueprint `tex/`, `blueprint/`, prose docstrings that carry the
owner's blueprint voice) touched on branch `independent-repair`, with the old text, the new
text and the reason. Edits are kept minimal and in the original voice. Purely technical
Lean docstrings written during the repair (new declarations, GAP labels) are not listed
here; they are listed in `ref/independent-repair-progress.md`.

---

## 1. `tex/statements/challenge-statement.tex` — `lem:stable-chart-at-instance`

**Why.** The block said the `StableChartAt` instance "currently stands as an open
obligation". It was never open: chart stability is false on every compact connected
Riemann surface (`not_chartStable_of_compactSpace`, compiled). The class and instance are
deleted (goal (a)).

**Old.**
> Chart-stability adapter instance (open). The `StableChartAt` adapter instance threaded
> through the public manifold / Lie structure of Jac(X). It currently stands as an open
> obligation (`sorry`) in `Jacobian/Solution.lean`; the honest route replaces it with
> genuine chart-overlap-derivative continuity (worker jc3). Tracking: #237.
> `\lean{…instStableChartAt…}`

**New.**
> Chart-stability adapter instance (retired: refuted). The `StableChartAt` adapter
> instance used to be threaded through the public manifold / Lie structure of Jac(X). It
> is not an open obligation but a false one: no compact connected Riemann surface has
> chart stability, and this is now a proved theorem (`not_chartStable_of_compactSpace`).
> The instance and the class are deleted; the few places that really used them now carry
> honest, labelled gaps, and the honest route is genuine chart-overlap-derivative
> continuity (worker jc3). Tracking: #237. `\lean{…not_chartStable_of_compactSpace}`
> `\leanok`

The sentence "the honest route replaces it with genuine chart-overlap-derivative
continuity" is kept in substance.

## 2. `scripts/audit-leanok-axioms.py:8-9` (docstring example)

**Why.** The example named "the open `StableChartAt` instance", which no longer exists.

**Old.** `… -> the open \`StableChartAt\` instance).`
**New.** `… -> an open \`sorry\` declaration).`

## Goal (b)–(d): blueprint blocks whose Lean target changed or was retired

All edits below keep the original sentence(s) and add at most one sentence in the same voice;
`\lean{}` pointers to retired declarations were removed or re-pointed. Line numbers are at the
time of the edit.

### 3. `tex/sections/04-branched-covers-genus-zero.tex:839`

**Why.** Lean decl retired (goal (a): eval-at-1 global frame).

**Old.**
```latex
Riemann surface admits a pointwise limit at every point of \(X\).
\lean{JacobianChallenge.HolomorphicForms.holomorphicOneForm_supNorm_cauchySeq_pointwise_limit_exists}
\leanok
```
**New.**
```latex
Riemann surface admits a pointwise limit at every point of \(X\).
\textit{Retired from the Lean development: the proof read 1-forms against the constant
\(1\) in every chart, which needs a global tangent frame (the refuted chart-stability
property). The classical statement stands; finiteness of \(H^0(X,\Omega^1)\) is now a named
classical input.}
```

### 4. `tex/sections/04-branched-covers-genus-zero.tex:855`

**Why.** Lean decl retired (goal (a)).

**Old.**
```latex
1-forms is continuous.
\lean{JacobianChallenge.HolomorphicForms.holomorphicOneForm_supNorm_cauchySeq_limit_continuous}
\leanok
```
**New.**
```latex
1-forms is continuous.
\textit{Retired from the Lean development: the proof read 1-forms against the constant
\(1\) in every chart, which needs a global tangent frame (the refuted chart-stability
property). The classical statement stands; finiteness of \(H^0(X,\Omega^1)\) is now a named
classical input.}
```

### 5. `tex/sections/04-branched-covers-genus-zero.tex:870`

**Why.** Lean decl retired (goal (a)).

**Old.**
```latex
1-forms is holomorphic.
\lean{JacobianChallenge.HolomorphicForms.holomorphicOneForm_supNorm_cauchySeq_limit_holomorphic}
\leanok
```
**New.**
```latex
1-forms is holomorphic.
\textit{Retired from the Lean development: the proof read 1-forms against the constant
\(1\) in every chart, which needs a global tangent frame (the refuted chart-stability
property). The classical statement stands; finiteness of \(H^0(X,\Omega^1)\) is now a named
classical input.}
```

### 6. `tex/sections/05-polygonal-model.tex:433`

**Why.** Lean decl retired with gaps 16/17 (goal (d)).

**Old.**
```latex
\code{Jacobian/Periods/AnalyticGenusEqTopologicalGenus.lean}.}
\lean{JacobianChallenge.Periods.analyticGenus_eq_topologicalGenus}
\leanok
```
**New.**
```latex
\code{Jacobian/Periods/AnalyticGenusEqTopologicalGenus.lean}.}
\textit{The Lean assembly is retired: it rested on the de Rham / Hodge statements of
section~6, which were false as stated on the project's surrogate form type (gaps 16, 17).
The public Jacobian needs only the analytic genus.}
```

### 7. `tex/sections/05-polygonal-model.tex:451`

**Why.** Gap 10 retired (false as stated, unreachable).

**Old.**
```latex
\begin{lemma}[Cut along non-tree edges yields an unfolded disk (open)]
\label{lem:cut-along-non-tree-yields-unfolded-disk}
Cutting a triangulated compact surface along the non-tree edges of a dual
spanning tree produces a disk (the fundamental polygon). Open obligation
(\code{sorry}) in the Lean development.
Tracking: \ghissue{226}.
\lean{JacobianChallenge.Periods.cut_along_nonTree_yields_unfoldedDisk}
```
**New.**
```latex
\begin{lemma}[Cut along non-tree edges yields an unfolded disk (retired)]
\label{lem:cut-along-non-tree-yields-unfolded-disk}
Cutting a triangulated compact surface along the non-tree edges of a dual
spanning tree produces a disk (the fundamental polygon). The Lean statement had
placeholder (\code{PUnit}) hypotheses and was false as stated, so it is retired
(\code{Attic/FalseGaps}); the classical statement is not on the path of the public Jacobian.
Tracking: \ghissue{226}.
```

### 8. `tex/sections/05-polygonal-model.tex:554`

**Why.** Gap 9 retired (false as stated, unreachable).

**Old.**
```latex
\begin{lemma}[Handle-prefix tail-rotation homeomorphism (open)]
\label{lem:handleprefix-tailrotate-homeomorph}
Rotating the tail of a handle-prefixed edge word gives a homeomorphic quotient
(a Tietze handle-swap step in the surface classification). Open obligation
(\code{sorry}).
Tracking: \ghissue{239}.
\lean{JacobianChallenge.Periods.handlePrefix_tailRotate_homeomorph_nonzero}
```
**New.**
```latex
\begin{lemma}[Handle-prefix tail-rotation homeomorphism (retired)]
\label{lem:handleprefix-tailrotate-homeomorph}
Rotating the tail of a handle-prefixed edge word gives a homeomorphic quotient
(a Tietze handle-swap step in the surface classification). The Lean statement asked
for a self-homeomorphism of the disk conjugating the two side pairings, which does not
exist in general (gap 9), so it is retired (\code{Attic/FalseGaps}).
Tracking: \ghissue{239}.
```

### 9. `tex/sections/06-periods-and-riemann-bilinear.tex:728`

**Why.** Gap 16 retired.

**Old.**
```latex
\begin{lemma}[Zero-period closed form is exact (open)]
\label{lem:de-rham-comparison-map1-zero-period-primitive-exists-provider}
A closed \(1\)-form whose de Rham comparison image (all periods) vanishes admits
a global primitive, hence is exact. Open obligation (\code{sorry}).
Tracking: \ghissue{242}.
\lean{JacobianChallenge.HolomorphicForms.deRhamComparisonMap1_zero_period_primitiveExists_provider}
```
**New.**
```latex
\begin{lemma}[Zero-period closed form is exact (retired)]
\label{lem:de-rham-comparison-map1-zero-period-primitive-exists-provider}
A closed \(1\)-form whose de Rham comparison image (all periods) vanishes admits
a global primitive, hence is exact. The Lean statement lived on a surrogate form type
with \(d := 0\), where it said \(H^0(X,\Omega^1)=0\) — false for \(g\ge 1\) (gap 16) — so it
is retired (\code{Attic/FalseGaps}).
Tracking: \ghissue{242}.
```

### 10. `tex/sections/06-periods-and-riemann-bilinear.tex:743`

**Why.** Dependents of gap 16 retired.

**Old.**
```latex
zero-period primitive-existence provider.
\lean{JacobianChallenge.HolomorphicForms.deRhamComparisonMap1_zero_period_exact_axiom_frontier,
JacobianChallenge.HolomorphicForms.deRhamComparisonMap1_zero_period_mem_exact_frontier,
JacobianChallenge.HolomorphicForms.deRhamComparisonMap1_comparison_kernel_mem_exact_of_zero_period_frontier,
JacobianChallenge.HolomorphicForms.deRhamComparisonMap1_comparison_kernel_mem_exact_frontier}
```
**New.**
```latex
zero-period primitive-existence provider. \textit{Retired with gap 16.}
```

### 11. `tex/sections/06-periods-and-riemann-bilinear.tex:759`

**Why.** Gap 17 retired.

**Old.**
```latex
\begin{lemma}[Zero-harmonic closed form is exact (open)]
\label{lem:hodge-remainder-period-payload-exact}
A closed \(1\)-form with zero harmonic projection is exact (the Hodge-remainder
exactness payload). Open obligation (\code{sorry}).
Tracking: \ghissue{243}.
\lean{JacobianChallenge.HolomorphicForms.hodgeRemainder_periodPayload_exact}
```
**New.**
```latex
\begin{lemma}[Zero-harmonic closed form is exact (retired)]
\label{lem:hodge-remainder-period-payload-exact}
A closed \(1\)-form with zero harmonic projection is exact (the Hodge-remainder
exactness payload). The Lean statement on the surrogate form type said
\(\mathrm{Hom}(H_1(X,\Z),\C)=0\) — false for \(g\ge 1\), and contradicting gap 16 — so it is
retired (\code{Attic/FalseGaps}).
Tracking: \ghissue{243}.
```

### 12. `tex/sections/06-periods-and-riemann-bilinear.tex:775`

**Why.** Dependents of gap 17 retired.

**Old.**
```latex
analytic frontier is the Hodge-remainder period-payload exactness input.
\lean{JacobianChallenge.HolomorphicForms.harmonicProjection1_hodgeDecomposition,
JacobianChallenge.HolomorphicForms.harmonicProjection1_kernel_subset_exact,
JacobianChallenge.HolomorphicForms.harmonicProjection1_kernel_eq_exact}
```
**New.**
```latex
analytic frontier is the Hodge-remainder period-payload exactness input.
\textit{Retired with gap 17.}
```

### 13. `tex/sections/06-periods-and-riemann-bilinear.tex:813`

**Why.** Lattice is now genuine; old Type-0 decl retired.

**Old.**
```latex
\uses{input:riemann-bilinear, def:period-pairing, thm:analytic-eq-topological-genus, lem:h1-basis-of-compact-riemann-surface-u, lem:riemann-classical-real-li-input-u}
The image \(\periods_X := \Pi_X(H_1(X,\Z))\) is a full lattice in the
real vector space underlying \(\HdualX\).
\lean{JacobianChallenge.Periods.periodFullComplexLattice}
```
**New.**
```latex
\uses{input:riemann-bilinear, def:period-pairing}
The image \(\periods_X := \Pi_X(H_1(X,\Z))\) is a full lattice in the
real vector space underlying \(\HdualX\).
In Lean, \(\periods_X\) is generated by the integrals of the basis forms over closed
\(C^1\) curves, and its discreteness and fullness are the named classical input
\code{periodLattice\_discrete\_and\_span}.
\lean{JacobianChallenge.Periods.genuinePeriodLattice, JacobianChallenge.Periods.periodLattice_discrete_and_span}
```

### 14. `tex/sections/06-periods-and-riemann-bilinear.tex:831`

**Why.** Gap 3 chain retired (goal (b)).

**Old.**
```latex
\begin{lemma}[Universe-$u$ $H_1$ basis (open)]
\label{lem:h1-basis-of-compact-riemann-surface-u}
A \(\Z\)-basis of \(H_1\) for a universe-\(u\) compact Riemann surface
(\(\code{IntegralOneCycleU}\)). Open obligation (\code{sorry}).
Tracking: \ghissue{240}.
\lean{JacobianChallenge.Periods.h1_basis_of_compact_riemann_surfaceU}
```
**New.**
```latex
\begin{lemma}[Universe-$u$ $H_1$ basis (retired)]
\label{lem:h1-basis-of-compact-riemann-surface-u}
A \(\Z\)-basis of \(H_1\) for a universe-\(u\) compact Riemann surface
(\(\code{IntegralOneCycleU}\)). No longer needed: the period lattice is generated by
integrals over closed curves directly, and its rank is a classical input; the Lean
statement is retired with the zero-pairing chain (\code{Attic/ZeroPeriodPairingU}).
Tracking: \ghissue{240}.
```

### 15. `tex/sections/06-periods-and-riemann-bilinear.tex:840`

**Why.** Gap 15 retired (goal (b)).

**Old.**
```latex
\begin{lemma}[Universe-$u$ Riemann-bilinear $\R$-LI input (open)]
\label{lem:riemann-classical-real-li-input-u}
Universe-\(u\) companion of the Riemann-bilinear \(\R\)-linear-independence
input. Open obligation (\code{sorry}).
Tracking: \ghissue{241}.
\lean{JacobianChallenge.Periods.riemann_classical_real_LI_inputU}
```
**New.**
```latex
\begin{lemma}[Universe-$u$ Riemann-bilinear $\R$-LI input (retired)]
\label{lem:riemann-classical-real-li-input-u}
Universe-\(u\) companion of the Riemann-bilinear \(\R\)-linear-independence
input. Stated against the zero period pairing it was false for \(g\ge1\) (gap 15); it is
retired, and the content now lives in the classical input
\code{periodLattice\_discrete\_and\_span}.
Tracking: \ghissue{241}.
```

### 16. `tex/sections/08-abel-jacobi-map.tex:63`

**Why.** Pointer moved to the genuine (now proved) path-independence lemma.

**Old.**
```latex
from \(P\) to \(Q\).
\lean{JacobianChallenge.AbelJacobi.analyticOfCurve}
\leanok
```
**New.**
```latex
from \(P\) to \(Q\).
\lean{JacobianChallenge.AbelJacobi.pathIntegralFunctionalU_sub_mem, JacobianChallenge.AbelJacobi.analyticOfCurveU_eq_mk_periodVector}
\leanok
```

### 17. `tex/sections/08-abel-jacobi-map.tex:486`

**Why.** Type-0 decl retired; points at the universe-u assembly; gap labelled as classical input.

**Old.**
```latex
signature. Open obligation (\code{sorry}) until the genus-zero single-pole
route lands. Consumed by the challenge API (\ref{thm:challenge-api}).
Tracking: \ghissue{224}.
\lean{JacobianChallenge.AbelJacobi.analyticOfCurve_injective}
```
**New.**
```latex
signature. The point-separation theorem stands as the named classical input
\code{pathIntegralFunctional\_separates\_pointsU} (Abel's theorem, two-point form).
Consumed by the challenge API (\ref{thm:challenge-api}).
Tracking: \ghissue{224}.
\lean{JacobianChallenge.AbelJacobi.analyticOfCurve_injectiveU}
```

### 18. `tex/sections/09-degree-trace-push-pull.tex:101`

**Why.** Pointer fix: the Type-0 analyticPushforward is retired; the trace map itself is traceFormsBundledLM.

**Old.**
```latex
\lean{JacobianChallenge.TraceDegree.analyticPushforward,JacobianChallenge.HolomorphicForms.trace_pullback_at_regular_value,JacobianChallenge.HolomorphicForms.traceFormsBundled_eq_zero_of_constant}
```
**New.**
```latex
\lean{JacobianChallenge.HolomorphicForms.traceFormsBundledLM,JacobianChallenge.HolomorphicForms.trace_pullback_at_regular_value,JacobianChallenge.HolomorphicForms.traceFormsBundled_eq_zero_of_constant}
```

### 19. `tex/sections/09-degree-trace-push-pull.tex:221`

**Why.** Type-0 decl retired; point at the universe-u identity used by Solution.

**Old.**
```latex
\lean{JacobianChallenge.TraceDegree.analyticPushforward_analyticPullback}
```
**New.**
```latex
\lean{JacobianChallenge.TraceDegree.analyticPushforward_analyticPullbackU}
```

### 20. `tex/sections/04-branched-covers-genus-zero.tex:975`

**Why.** Pre-existing broken pointers: namespace prefix added (no prose change).

**Old.**
```latex
\lean{JacobianChallenge.HolomorphicForms.ContMDiffSection_localRepr_identityChart_contDiff,identityChartCoeff_contDiff,identityChartCoeff_tendsto_zero}
```
**New.**
```latex
\lean{JacobianChallenge.HolomorphicForms.ContMDiffSection_localRepr_identityChart_contDiff,JacobianChallenge.HolomorphicForms.identityChartCoeff_contDiff,JacobianChallenge.HolomorphicForms.identityChartCoeff_tendsto_zero}
```

### 21. `tex/sections/09-degree-trace-push-pull.tex:66`

**Why.** Pre-existing broken pointer to a non-existent (zero-pairing) lemma dropped (no prose change).

**Old.**
```latex
\lean{JacobianChallenge.TraceDegree.pullbackFormsLinearMap,periodPairing_pullbackFormsBundledLM}
```
**New.**
```latex
\lean{JacobianChallenge.TraceDegree.pullbackFormsLinearMap}
```

---

## Cleanup pass (2026-10-28): pointers to removed placeholder declarations

### 22. `tex/sections/08-abel-jacobi-map.tex:248`

**Why.** Lean decl removed with the placeholder Abel scaffold (Unit witnesses); \lean/\leanok dropped, one sentence added.

**Old.**
```latex
principal divisor is \((Q_1) - (Q_2)\). In particular, the pole
divisor of \(f\) equals the single point \((Q_2)\).
\lean{JacobianChallenge.AbelJacobi.abelJacobi_image_zero_implies_principal}
\leanok
\end{theorem}
```
**New.**
```latex
principal divisor is \((Q_1) - (Q_2)\). In particular, the pole
divisor of \(f\) equals the single point \((Q_2)\).
Not formalized: the former Lean statement was built on placeholder
(\code{Unit}-witness) Abel data and has been removed; Abel's theorem
enters as the classical input \code{pathIntegralFunctional\_separates\_pointsU}.
\end{theorem}
```

### 23. `tex/sections/08-abel-jacobi-map.tex:271`

**Why.** Proof \leanok dropped (its Lean proof was removed with the placeholder scaffold).

**Old.**
```latex
\begin{proof}\leanok
Pure assembly of Lemma~\ref{lem:abel-two-point-form}
```
**New.**
```latex
\begin{proof}
Pure assembly of Lemma~\ref{lem:abel-two-point-form}
```

### 24. `tex/sections/08-abel-jacobi-map.tex:298`

**Why.** Lean decl removed with the placeholder Abel scaffold; \lean/\leanok dropped, one sentence added.

**Old.**
```latex
difference of the two points).
\lean{JacobianChallenge.AbelJacobi.abel_meromorphicFunction_of_zero_aj_two_point}
\leanok
\end{lemma}
```
**New.**
```latex
difference of the two points).
Not formalized: the former Lean statement was built on placeholder
(\code{Unit}-witness) Abel data and has been removed.
\end{lemma}
```

### 25. `tex/sections/08-abel-jacobi-map.tex:450`

**Why.** Type-0 decl (built on placeholder Abel data) removed; pointer moved to the universe-polymorphic statement (classical input C3).

**Old.**
```latex
If \(g(X)>0\) and \(\AJ_P(Q_1)=\AJ_P(Q_2)\), then \(Q_1=Q_2\).
\lean{JacobianChallenge.AbelJacobi.pathIntegralFunctional_separates_points}
\leanok
\end{theorem}
```
**New.**
```latex
If \(g(X)>0\) and \(\AJ_P(Q_1)=\AJ_P(Q_2)\), then \(Q_1=Q_2\).
\lean{JacobianChallenge.AbelJacobi.pathIntegralFunctional_separates_pointsU}
\leanok
\end{theorem}
```

### 26. `tex/sections/08-abel-jacobi-map.tex:472`

**Why.** Proof \leanok dropped: the Lean statement is the classical input C3 (no Lean proof).

**Old.**
```latex
\begin{proof}\leanok
Assume \(Q_1\ne Q_2\).
```
**New.**
```latex
\begin{proof}
Assume \(Q_1\ne Q_2\).
```

### 27. `tex/sections/08-abel-jacobi-map.tex:510`

**Why.** Pointer moved from the removed Type-0 decl to the universe-polymorphic classical input C3.

**Old.**
```latex
\(\AJ_P(Q_1)=\AJ_P(Q_2)\), then \(Q_1=Q_2\).
\lean{JacobianChallenge.AbelJacobi.pathIntegralFunctional_separates_points}
\end{theorem}
```
**New.**
```latex
\(\AJ_P(Q_1)=\AJ_P(Q_2)\), then \(Q_1=Q_2\).
\lean{JacobianChallenge.AbelJacobi.pathIntegralFunctional_separates_pointsU}
\end{theorem}
```

### 28. `tex/sections/06-periods-and-riemann-bilinear.tex:306`

**Why.** Lean decl was a True-valued placeholder; removed, \lean/\leanok dropped, sentence names the local exactness lemma actually used.

**Old.**
```latex
atlas.}
\lean{JacobianChallenge.Blueprint.holomorphic_form_is_closed}
\leanok
\end{lemma}
\begin{proof}\leanok\end{proof}
```
**New.**
```latex
atlas.}
Not formalized as stated: the former Lean statement was a placeholder (its type was
\code{True}) and has been removed. The project uses the local form instead: on a
coordinate ball a holomorphic 1-form has a primitive (\code{chartForm\_hasFDerivAt\_primitive}).
\end{lemma}
```

### 29. `tex/sections/06-periods-and-riemann-bilinear.tex:338`

**Why.** Lean decl stated with zero-placeholder integrals (vacuous); removed, \lean/\leanok dropped, one sentence added.

**Old.**
```latex
per the project inventory.}
\lean{JacobianChallenge.Blueprint.Sec03.stokes_on_rs_with_boundary}
\leanok
\end{theorem}
\begin{proof}\leanok\end{proof}
```
**New.**
```latex
per the project inventory.}
Not formalized: the former Lean statement integrated with placeholder integrals
(\code{:= 0}) and has been removed.
\end{theorem}
```

### 30. `tex/sections/06-periods-and-riemann-bilinear.tex:721`

**Why.** Lean decl rested on the placeholder exteriorDerivative := 0; removed, \lean/\leanok dropped, one sentence added.

**Old.**
```latex
LinearMap.range (exteriorDerivative 0 X)}.}
\lean{JacobianChallenge.HolomorphicForms.deRhamComparisonMap1_zero_period_primitiveExists_exact_assembly}
\leanok
\end{lemma}
\begin{proof}\leanok\end{proof}
```
**New.**
```latex
LinearMap.range (exteriorDerivative 0 X)}.}
Not formalized: the former Lean statement used the placeholder
\code{exteriorDerivative := 0} and has been removed.
\end{lemma}
```

### 31. `tex/sections/08-abel-jacobi-map.tex:316`

**Why.** Proof \leanok dropped (Lean proof removed with the placeholder scaffold).

**Old.**
```latex
\begin{proof}\leanok
The substantive content is the classical Abel construction
```
**New.**
```latex
\begin{proof}
The substantive content is the classical Abel construction
```

---

## C4 removal (2026-10-28)

### 32. `tex/sections/04-branched-covers-genus-zero.tex:626`

**Why.** The lemma no longer rests on genus-zero uniformization; dependency edge removed.

**Old.**
```latex
\uses{thm:exists-biholomorph-one-point-of-genus-zero, lem:holomorphic-one-form-pullback-via-biholo}
```
**New.**
```latex
\uses{lem:holomorphic-one-form-pullback-via-biholo}
```

### 33. `tex/sections/04-branched-covers-genus-zero.tex:634`

**Why.** Proof paragraph replaced: the Lean proof now avoids uniformization (simple connectivity of the punctured sphere + covering space of primitives).

**Old.**
```latex
\begin{proof}\leanok
This is the genus-zero case of the uniformization theorem. Any
complex structure on the topological 2-sphere is biholomorphic to
the standard structure on \(\CPone=\code{OnePoint}\,\C\); the resulting
biholomorphism \(\psi:X\xrightarrow{\sim}\CPone\) pulls back
holomorphic 1-forms to holomorphic 1-forms, yielding the
\(\C\)-linear isomorphism
\(\psi^{*}:H^{0}(\CPone,\Omega^{1}_{\CPone})\to H^{0}(X,\Omega^{1}_{X})\).
\end{proof}
```
**New.**
```latex
\begin{proof}\leanok
Both spaces are zero, so any linear map between them is an isomorphism. For
\(X\): given two chart chains with the same endpoints, pick a point \(z\) they
both miss (Baire); \(X\setminus\{z\}\cong S^2\setminus\{\mathrm{pt}\}\cong\R^2\)
is simply connected, so \(\omega\) has a primitive there (lift through the
covering space of local primitives), and the two integrals agree. A form whose
integrals are path-independent vanishes (maximum principle). This avoids the
uniformization theorem.
\end{proof}
```

### 34. `tex/sections/04-branched-covers-genus-zero.tex:909`

**Why.** Lean decl (classical input C4) removed as unused; \lean dropped, one sentence added.

**Old.**
```latex
(\code{ContMDiff}).
Tracking: \ghissue{232}.
\lean{JacobianChallenge.HolomorphicForms.exists_biholomorph_onePoint_of_genus_zero}
\end{theorem}
```
**New.**
```latex
(\code{ContMDiff}).
Tracking: \ghissue{232}.
Not needed by the formal development: the genus statement uses
Lemma~\ref{lem:holomorphic-one-form-equiv-of-homeo-sphere}, proved without
uniformization; the former Lean statement (a named classical input) is removed.
\end{theorem}
```
