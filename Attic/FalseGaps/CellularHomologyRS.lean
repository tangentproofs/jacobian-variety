/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/Periods/CellularHomologyRS.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

theorem compactRiemannSurface_hasFiniteCWStructure
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (FiniteCWStructure X) := by
  -- 1. Bridge from complex 1-manifold to real 2-manifold
  obtain ⟨srStruct⟩ := ChartedSpaceComplex_to_smoothReal2 X
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) X := srStruct.chartedSpace
  letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) X := srStruct.isManifold
  -- 2. Riemann surfaces are orientable
  letI : Orientable X := ⟨⟨()⟩⟩
  -- 3. Apply the polygonal-model homeomorphism (surface classification)
  obtain ⟨g, ⟨homeo⟩⟩ := existsHomeoToPolygon4g X
  -- 4. Get the CW structure on Polygon4g g
  obtain ⟨cw⟩ := polygon4g_finiteCWStructure g
  -- 5. Transport along the homeomorphism
  exact ⟨finiteCWStructure_of_homeo homeo cw⟩

theorem cellularH1_finite_singularIsoData
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_cw : FiniteCWStructure X) :
    ∃ (CH1 : Type) (_ : AddCommGroup CH1) (_iCH1 : Module ℤ CH1)
      (_hF : Module.Finite ℤ CH1) (_hFr : Module.Free ℤ CH1),
      Nonempty (CH1 ≃ₗ[ℤ] IntegralOneCycle X) := by
  -- 1. Bridge from complex 1-manifold to real 2-manifold
  obtain ⟨srStruct⟩ := ChartedSpaceComplex_to_smoothReal2 X
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) X := srStruct.chartedSpace
  letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) X := srStruct.isManifold
  letI : Orientable X := ⟨⟨()⟩⟩
  -- 3. Apply the polygonal-model homeomorphism (surface classification)
  obtain ⟨g, ⟨homeo⟩⟩ := existsHomeoToPolygon4g X
  -- 4. Get the singular H₁ basis for the standard fundamental polygon
  obtain ⟨b⟩ := polygon4g_singularH1_basis g
  -- 5. Construct the cellular H₁ witness type and the isomorphism
  let CH1 := Fin (2 * g) → ℤ
  let e_singular := b.equivFun.symm.trans (singularH1LinearEquivOfHomeo homeo.symm)
  -- v4.31 no longer infers Module.Finite/Free ℤ (Fin _ → ℤ) through the `let`;
  -- supply the Pi instances explicitly.
  refine ⟨CH1, inferInstanceAs (AddCommGroup (Fin (2 * g) → ℤ)),
    inferInstanceAs (Module ℤ (Fin (2 * g) → ℤ)),
    Module.Finite.pi, Module.Free.pi ℤ _, ⟨e_singular⟩⟩

/--
Derived from `cellularH1_finite_singularIsoData` by forgetting the
finiteness/freeness witnesses.
-/
theorem cellular_iso_singular_h1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (cw : FiniteCWStructure X) :
    ∃ (CH1 : Type) (_ : AddCommGroup CH1) (_ : Module ℤ CH1),
      Nonempty (CH1 ≃ₗ[ℤ] IntegralOneCycle X) := by
  obtain ⟨CH1, hAb, hMod, _, _, hIso⟩ := cellularH1_finite_singularIsoData X cw
  exact ⟨CH1, hAb, hMod, hIso⟩

theorem IntegralOneCycle_finite_of_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (cw : FiniteCWStructure X) :
    Module.Finite ℤ (IntegralOneCycle X) := by
  obtain ⟨_, _, _, _hF, _, hIso⟩ := cellularH1_finite_singularIsoData X cw
  exact Module.Finite.equiv hIso.some

theorem IntegralOneCycle_free_of_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (cw : FiniteCWStructure X) :
    Module.Free ℤ (IntegralOneCycle X) := by
  obtain ⟨_, _, _, _, _hFr, hIso⟩ := cellularH1_finite_singularIsoData X cw
  exact Module.Free.of_equiv hIso.some

theorem IntegralOneCycle_finite_via_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.Finite ℤ (IntegralOneCycle X) := by
  obtain ⟨cw⟩ := compactRiemannSurface_hasFiniteCWStructure X
  exact IntegralOneCycle_finite_of_cellular X cw

theorem IntegralOneCycle_torsionFree_via_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.Free ℤ (IntegralOneCycle X) := by
  obtain ⟨cw⟩ := compactRiemannSurface_hasFiniteCWStructure X
  exact IntegralOneCycle_free_of_cellular X cw
