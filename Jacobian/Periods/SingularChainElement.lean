import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.PrismChainBridge
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Singular chain element extraction

Concrete construction sending a continuous singular `n`-simplex
`σ : C(stdSimplex ℝ (Fin (n+1)), X)` to its chain-complex generator
`singularChainElement σ` inside Mathlib's `singularChainComplex`.

The chain group at level `n` is

`∐_{σ ∈ (TopCat.toSSet.obj X).obj ⦋n⦌ᵒᵖ} (ModuleCat.of ℤ ℤ)`

(definitionally, via `alternatingFaceMapComplex_obj_X` and the
unfolding of `sigmaConst`). The construction takes `σ`, transports it
through `TopCat.toSSetObjEquiv.symm`, and applies the canonical
coproduct injection `Sigma.ι` to the unit `(1 : ℤ)`.

## Status
-/

namespace JacobianChallenge.Periods

open AlgebraicTopology CategoryTheory CategoryTheory.Limits SimplexCategory Opposite
open Simplicial

/--
The chain group at level `n` of the singular chain complex of a
topological space `X` with coefficients in `ModuleCat.of ℤ ℤ`.
-/
noncomputable abbrev SingularChain (X : Type) [TopologicalSpace X] (n : ℕ) :
    ModuleCat ℤ :=
  (((singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)).X n

/--
The equivalence between continuous singular `n`-simplices on `X`
and the indexing type for the level-`n` chain group's coproduct.
-/
noncomputable def singularChainSimplexIndex
    (X : Type) [TopologicalSpace X] (n : ℕ) :
    C(stdSimplex ℝ (Fin (n + 1)), X) ≃
      (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) :=
  (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm

/--
The simplicial object underlying the singular chain complex,
exposed as a level-`n` lookup. By construction this is
`(sigmaConst.obj R).obj ((TopCat.toSSet.obj X).obj n)
 = ∐ (fun _ : (TopCat.toSSet.obj X).obj n => R)`.
-/
noncomputable abbrev SingularChainCoproduct
    (X : Type) [TopologicalSpace X] (n : ℕ) : ModuleCat ℤ :=
  ∐ (fun _ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) =>
    ModuleCat.of ℤ ℤ)

/--
Concretely: take `σ`, view it as an element of the simplicial set
via `singularChainSimplexIndex`, take the canonical coproduct
injection `Sigma.ι` at that index, and apply this `ModuleCat`-
morphism to the unit `(1 : ℤ)`.
-/
noncomputable def singularChainElement
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    SingularChainCoproduct X n :=
  let s : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) :=
    singularChainSimplexIndex X n σ
  (Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) =>
    ModuleCat.of ℤ ℤ) s).hom (1 : ℤ)

/--
The `i`-th topological face inclusion `stdSimplex ℝ (Fin (n+1)) →
stdSimplex ℝ (Fin (n+2))` as a continuous map, induced by
`Fin.succAbove i`. This is the geometric realisation of
`SimplexCategory.δ i`.
-/
noncomputable def stdSimplexFaceMap
    (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map (Fin.succAbove i), stdSimplex.continuous_map _⟩

/--
The face of a singular `(n+1)`-simplex obtained by precomposition
with the i-th face inclusion.
-/
noncomputable def singularSimplexFace
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (σ : C(stdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), X) :=
  σ.comp (stdSimplexFaceMap n i)

/--
Naturality lemma: the simplicial face map on the singular
simplicial set composed with `Sigma.ι` equals `Sigma.ι` of the face
of the simplex.

This is a key intermediate step for the boundary decomposition: it
says the face action commutes with the coproduct injection. The
result is stated at the morphism level (compositions in the category
`ModuleCat ℤ`); it follows directly from `Sigma.ι_comp_map'`.
-/
lemma sigmaConst_obj_map_ι
    {α β : Type} (f : α → β) (a : α) :
    (Sigma.ι (fun _ : α => ModuleCat.of ℤ ℤ) a : _ ⟶ _)
        ≫ Sigma.map' f (fun _ => 𝟙 (ModuleCat.of ℤ ℤ))
      = Sigma.ι (fun _ : β => ModuleCat.of ℤ ℤ) (f a) := by
  rw [Sigma.ι_comp_map', Category.id_comp]

/--
`d_{n+1} (singularChainElement σ) =
    ∑_{i : Fin (n+2)} (-1)^i • singularChainElement (singularSimplexFace σ i)`.

This unfolds `alternatingFaceMapComplex` (whose `objD = ∑ (-1)^i • δ_i`)
and uses the naturality of `Sigma.ι` under `Sigma.map'` (i.e.,
`Sigma.ι_comp_map'`) to commute the simplicial face map past the
coproduct injection. Each step is mechanical Mathlib bookkeeping;
the proof is a roughly 30-50 line categorical computation that fits
inside this file (no new infrastructure required).
-/
theorem singularChainElement_boundary_decomposition
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 2)), X)) :
    (((singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)).d (n + 1) n
        (singularChainElement σ : SingularChainCoproduct X (n + 1)) =
      ((Finset.univ : Finset (Fin (n + 2))).sum
        fun i => ((-1 : ℤ) ^ (i : ℕ)) •
          (singularChainElement (singularSimplexFace σ i) :
            SingularChainCoproduct X n)) := by
  -- The chain differential of `singularChainElement σ` decomposes as
  -- the alternating sum of face inclusions. We use the morphism-level
  -- identity `singChain_d_basis` from `PrismChainBridge` and apply
  -- it at the unit `(1 : ℤ)`.
  --
  -- Key API:
  --   * `singChain_d_basis n σ` — the morphism-level identity.
  --   * `ModuleCat.comp_apply` — `(f ≫ g) x = g (f x)`.
  --   * `ModuleCat.hom_sum` and `ModuleCat.hom_zsmul` — linearity of
  --     `.hom` over Finset sums and zsmul.
  -- The element-level transformation is mechanical from the morphism
  -- identity.
  have hMorphism := singChain_d_basis n σ
  -- Apply both sides at `(1 : ℤ)` via congr_arg using ModuleCat coercion.
  have hElem :
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)).d (n + 1) n
          ((singChain_basis σ : ModuleCat.of ℤ ℤ ⟶ singChain (n + 1) X)
            (1 : ℤ)) =
      ((∑ j : Fin (n + 2), ((-1 : ℤ) ^ j.val) •
          singChain_basis (σ.comp (stdSimplexFaceInclusion n j)))
            : ModuleCat.of ℤ ℤ ⟶ singChain n X) (1 : ℤ) := by
    rw [← ModuleCat.comp_apply, hMorphism]
  -- Recognise `(singChain_basis σ) 1 = singularChainElement σ`.
  have h_basis_eq :
      (singChain_basis σ : ModuleCat.of ℤ ℤ ⟶ singChain (n + 1) X) (1 : ℤ) =
      (singularChainElement σ : SingularChainCoproduct X (n + 1)) := rfl
  rw [h_basis_eq] at hElem
  -- Rewrite RHS sum-of-morphisms applied at 1 into a sum of element-level
  -- terms via `ModuleCat.hom_sum` and `ModuleCat.hom_zsmul`.
  rw [hElem]
  -- Now show the RHS shape matches.
  -- The RHS is `(∑ j, (-1)^j • singChain_basis (σ.comp (stdSimplexFaceInclusion n j))) 1`.
  -- Via ModuleCat coercion this equals `((∑ ...).hom) 1 = ∑ j, ((-1)^j • singChain_basis ...).hom 1`.
  -- Then `((-1)^j • -).hom 1 = (-1)^j • (- : ...).hom 1 = (-1)^j • singularChainElement (...)`.
  show (((∑ j : Fin (n + 2), ((-1 : ℤ) ^ j.val) •
            singChain_basis (σ.comp (stdSimplexFaceInclusion n j)))
            : ModuleCat.of ℤ ℤ ⟶ singChain n X).hom (1 : ℤ) : SingularChainCoproduct X n) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (singularChainElement (singularSimplexFace σ i) :
          SingularChainCoproduct X n)
  rw [ModuleCat.hom_sum]
  rw [LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ModuleCat.hom_zsmul]
  -- After the rewrites, the goal is:
  --   ((-1)^i • Hom.hom (singChain_basis ...)) 1 = (-1)^i • singularChainElement (...)
  -- The goal is solved by definition or by the default simp set.
  simp only []
  -- Now: (-1)^i • Hom.hom (singChain_basis ...) 1 = (-1)^i • singularChainElement (...)
  -- The Hom.hom application reduces to singularChainElement by definition.
  rfl


end JacobianChallenge.Periods

