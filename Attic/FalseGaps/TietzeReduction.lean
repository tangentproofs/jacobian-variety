/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/Periods/TietzeReduction.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

theorem orientable_letterPair_opposite_orientation
    {M : Type} [TopologicalSpace M] [Orientable M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus)
    (_hw : EdgeWord.WordEq E.word w) :
    ∀ ℓ : Letter E.extractedGenus, ℓ ∈ w → ℓ.inv ∈ w := by
  sorry

theorem orientable_handleSwap_grouping
    {g : ℕ} (w : EdgeWord g)
    (_hPairs : ∀ ℓ : Letter g, ℓ ∈ w → ℓ.inv ∈ w)
    (_hReduced : ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel w x) :
    ∃ v : EdgeWord g, EdgeWord.TietzeEq w v ∧
      (∃ perm : Equiv.Perm (Fin g), v = (List.finRange g).flatMap (fun i => EdgeWord.handleBlock (perm i))) := by
  sorry

/--
**Core Brahana lemma (orientable handle separation).**  Given that
`w` is the cyclic reduction of the boundary word `E.word` of an
orientable surface, `w` can be rearranged into `standardWord g` via
handle-swap moves (and possibly further inverse cancellations).
-/
private lemma brahana_orientable_core
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus)
    (hReduced : ∀ x : EdgeWord E.extractedGenus, ¬ EdgeWord.InverseCancel w x)
    (hWordEq : EdgeWord.WordEq E.word w) :
    EdgeWord.TietzeEq w (EdgeWord.standardWord E.extractedGenus) := by
  have hPairs := orientable_letterPair_opposite_orientation E w hWordEq
  obtain ⟨v, hwv, hGrouped⟩ := orientable_handleSwap_grouping w hPairs hReduced
  have hvs := handleSwap_index_ordering v hGrouped
  exact hwv.trans hvs

theorem rawWord_handle_separation_orientable
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus)
    (_hReduced : ∀ x : EdgeWord E.extractedGenus, ¬ EdgeWord.InverseCancel w x)
    (hWordEq : EdgeWord.WordEq E.word w) :
    ∃ v : EdgeWord E.extractedGenus, EdgeWord.TietzeEq w v ∧
      v = EdgeWord.standardWord E.extractedGenus :=
  ⟨EdgeWord.standardWord E.extractedGenus,
   brahana_orientable_core E w _hReduced hWordEq,
   rfl⟩

/--
Bottom-up content: the classical Brahana / Seifert–Threlfall
reduction.
-/
theorem rawWord_tietzeEq_standardWord_orientable
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus)
    (hw : w = E.word) :
    EdgeWord.TietzeEq w (EdgeWord.standardWord E.extractedGenus) := by
  subst hw
  obtain ⟨v, hwv, hRed⟩ := rawWord_cyclic_reduction E.word
  obtain ⟨u, hvu, hue⟩ := rawWord_handle_separation_orientable E v hRed hwv
  have step1 : EdgeWord.TietzeEq E.word v := hwv.toTietzeEq
  exact step1.trans (hue ▸ hvu)

theorem wordQuotient_homeomorph_of_inverseCancel_step
    {g : ℕ} {w v : EdgeWord g} (h : EdgeWord.InverseCancel w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  -- Topology of inverse cancellation: quotient invariance directly.
  -- This replaces the false disk-lift `inverseCancel_geometric_maps`.
  sorry

/--
Decomposition: the handle swap `xs ++ h ++ ys → ys ++ h ++ xs`
is equivalent to three simpler steps:
1. Cyclic rotation by `|xs|`: `xs ++ h ++ ys → h ++ (ys ++ xs)`
2. Handle-prefix tail rotation by `|ys|`: `h ++ (ys ++ xs) → h ++ (xs ++ ys)`
3. Cyclic rotation by `|h| + |xs|`: `h ++ xs ++ ys → ys ++ h ++ xs`

Cyclic rotation is realised by a rigid rotation of the closed unit disk.
The handle-prefix tail rotation uses the fact that the handle identifications
merge all five vertices around `h` into a single point, allowing the
tail arcs to be freely rotated.
-/
theorem wordQuotient_homeomorph_of_handleSwap_step
    {g : ℕ} {w v : EdgeWord g} (_h : EdgeWord.HandleSwap w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  exact wordQuotient_homeomorph_of_handleSwap_step_v2 _h

/--
This is the last non-geometric part of quotient invariance: after this
the only remaining obligations are the two one-step homeomorphism
constructions, one for inverse cancellation and one for handle swap.
-/
theorem wordQuotient_homeomorph_of_tietzeStep
    {g : ℕ} {w v : EdgeWord g} (h : EdgeWord.TietzeStep w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  cases h with
  | cancel hc => exact wordQuotient_homeomorph_of_inverseCancel_step hc
  | swap hs => exact wordQuotient_homeomorph_of_handleSwap_step hs
  | rotate k => exact wordQuotient_homeomorph_of_rotate _ k

theorem wordQuotient_homeomorph_of_tietzeEq
    {g : ℕ} {w v : EdgeWord g} (h : EdgeWord.TietzeEq w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  -- Each `EdgeWord.TietzeStep` is either a `cancel`, `swap`, or `rotate`
  -- step; the corresponding leaf produces the homeomorphism. Compose
  -- along the reflexive-transitive closure.
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact ⟨Homeomorph.refl _⟩
  · intro _a _b hab _hbc ih
    obtain ⟨eab⟩ := wordQuotient_homeomorph_of_tietzeStep hab
    obtain ⟨ebv⟩ := ih
    exact ⟨eab.trans ebv⟩

/--
Strategy: extract the raw word `w`; produce three homeomorphisms
(M ≃ wordQuotient w via `edgeWord_wordQuotient_homeomorph_M`,
wordQuotient w ≃ wordQuotient (standardWord g) via the Tietze step,
wordQuotient (standardWord g) ≃ Polygon4g g via the standard-quotient
identification). Compose into `polyToM : Polygon4g g ≃ₜ M`, then take
`proj := polyToM ∘ Polygon4g.mk g` and verify `cts/surj/kernel` from
the homeomorphism + quotient API.
-/
noncomputable def EdgeWordPresentation.toPolygonalQuotient_via_tietze
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M]
    (E : EdgeWordPresentation M) : PolygonalQuotientPresentation M := by
  let w := E.word
  have htietze := rawWord_tietzeEq_standardWord_orientable E w rfl
  let homeoWord := Classical.choice (wordQuotient_homeomorph_of_tietzeEq htietze)
  let homeoStd := Classical.choice
    (standardWord_wordQuotient_homeomorph_polygon4g E.extractedGenus)
  let homeoM := Classical.choice (edgeWord_wordQuotient_homeomorph_M E w rfl)
  -- Compose: Polygon4g g ≃ₜ wordQuotient (standardWord g) ≃ₜ wordQuotient w ≃ₜ M.
  let polyToM : Polygon4g E.extractedGenus ≃ₜ M :=
    homeoStd.symm.trans (homeoWord.symm.trans homeoM)
  refine
    { genus := E.extractedGenus
      proj := fun z => polyToM (Polygon4g.mk E.extractedGenus z)
      cts := polyToM.continuous.comp continuous_quot_mk
      surj := polyToM.surjective.comp Quotient.mk_surjective
      kernel := ?_ }
  intro z w'
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact Quotient.exact (polyToM.injective h)
  · exact congrArg polyToM (Quotient.sound h)
