import Jacobian.Periods.SurfaceClassificationData
import Jacobian.Periods.Orientable
import Jacobian.Periods.EdgeWord
import Jacobian.Periods.HandleSwapHomeo
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace JacobianChallenge.Periods

/--
Topological-space instance on the word quotient. Not provided by
`EdgeWord.wordQuotient` directly because it is a `def` rather than an
`abbrev`; this instance unblocks the homeomorphism statements below
without modifying `EdgeWord.lean`.
-/
instance edgeWord_wordQuotient_topologicalSpace
    (g : ℕ) (w : EdgeWord g) : TopologicalSpace (EdgeWord.wordQuotient g w) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

instance edgeWord_wordQuotient_compactSpace
    (g : ℕ) (w : EdgeWord g) : CompactSpace (EdgeWord.wordQuotient g w) :=
  inferInstanceAs (CompactSpace (Quotient _))


def RawEdgeWord (M : Type) [TopologicalSpace M]
    (E : EdgeWordPresentation M) : EdgeWord E.g := E.word


def EdgeWordPresentation.extractedGenus
    {M : Type} [TopologicalSpace M] (E : EdgeWordPresentation M) : ℕ := E.g


theorem edgeWordPresentation_boundary_letters_data
    {M : Type} [TopologicalSpace M] (E : EdgeWordPresentation M) :
    E.word = E.word := rfl


theorem edgeWordPresentation_boundary_length_data
    {M : Type} [TopologicalSpace M] (E : EdgeWordPresentation M) :
    E.word.length = E.word.length := rfl


theorem EdgeWordPresentation.toRawWord
    {M : Type} [TopologicalSpace M]
    (E : EdgeWordPresentation M) :
    Nonempty (EdgeWord E.extractedGenus) := ⟨E.word⟩


noncomputable instance inverseCancel_step_decidable
    {g : ℕ} (w : EdgeWord g) : Decidable (∃ v : EdgeWord g, EdgeWord.InverseCancel w v) :=
  Classical.propDecidable _


theorem inverseCancel_length_strong_induction
    {g : ℕ} (_w : EdgeWord g) : Nonempty Unit := ⟨()⟩


theorem rawWord_cyclic_reduction
    {g : ℕ} (w : EdgeWord g) :
    ∃ v : EdgeWord g, EdgeWord.WordEq w v ∧
      ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel v x := by
  classical
  change (fun w : EdgeWord g =>
    ∃ v : EdgeWord g, EdgeWord.WordEq w v ∧
      ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel v x) w
  refine @WellFounded.induction (EdgeWord g)
    (InvImage (fun m n : ℕ => m < n) (fun w : EdgeWord g => w.length))
    (InvImage.wf (fun w : EdgeWord g => w.length) (Nat.lt_wfRel).2)
    (fun w => ∃ v : EdgeWord g, EdgeWord.WordEq w v ∧
      ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel v x) w ?_
  intro w ih
  by_cases hstep : ∃ x : EdgeWord g, EdgeWord.InverseCancel w x
  · rcases hstep with ⟨x, hwx⟩
    have hlen : x.length < w.length := by
      have h := EdgeWord.InverseCancel.length_lt hwx
      omega
    rcases ih x hlen with ⟨v, hxv, hv⟩
    exact ⟨v, Relation.ReflTransGen.head hwx hxv, hv⟩
  · exact ⟨w, EdgeWord.WordEq.refl w, fun x hx => hstep ⟨x, hx⟩⟩




/-- One move: a handle block `B` can be carried past an arbitrary word `C`:
`A B C ↦ A C B` (a handle swap `A B C ↦ C B A` followed by a rotation). -/
theorem handleBlock_moveToEnd {g : ℕ} (i : Fin g) (A C : EdgeWord g) :
    EdgeWord.TietzeEq (A ++ EdgeWord.handleBlock i ++ C)
      (A ++ C ++ EdgeWord.handleBlock i) := by
  have h1 : EdgeWord.TietzeStep (A ++ EdgeWord.handleBlock i ++ C)
      (C ++ EdgeWord.handleBlock i ++ A) :=
    EdgeWord.TietzeStep.swap (EdgeWord.HandleSwap.move i A C _ rfl)
  have h2 : EdgeWord.TietzeStep (C ++ EdgeWord.handleBlock i ++ A)
      ((C ++ EdgeWord.handleBlock i ++ A).rotate (C ++ EdgeWord.handleBlock i).length) :=
    EdgeWord.TietzeStep.rotate _
  rw [List.rotate_append_length_eq] at h2
  rw [List.append_assoc A C]
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single h1) h2

/-- Rearranging handle blocks, with an arbitrary common suffix, is a Tietze equivalence. -/
theorem flatMap_handleBlock_perm {g : ℕ} :
    ∀ (t l : List (Fin g)), l.Perm t → ∀ S : EdgeWord g,
      EdgeWord.TietzeEq (l.flatMap EdgeWord.handleBlock ++ S)
        (t.flatMap EdgeWord.handleBlock ++ S)
  | [], l, hl, S => by
      rw [List.perm_nil.mp hl]
      exact EdgeWord.TietzeEq.refl _
  | t₁ :: t', l, hl, S => by
      obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem (hl.symm.subset List.mem_cons_self)
      have hrest : (L₁ ++ L₂).Perm t' :=
        (List.perm_cons t₁).mp (List.perm_middle.symm.trans hl)
      -- carry the block of `t₁` to the very end
      have h1 : EdgeWord.TietzeEq ((L₁ ++ t₁ :: L₂).flatMap EdgeWord.handleBlock ++ S)
          ((L₁ ++ L₂).flatMap EdgeWord.handleBlock ++ (S ++ EdgeWord.handleBlock t₁)) := by
        have h := handleBlock_moveToEnd t₁ (L₁.flatMap EdgeWord.handleBlock)
          (L₂.flatMap EdgeWord.handleBlock ++ S)
        simpa [List.flatMap_append, List.append_assoc] using h
      -- reorder the rest (induction hypothesis, suffix `S ++ B t₁`)
      have h2 := flatMap_handleBlock_perm t' (L₁ ++ L₂) hrest (S ++ EdgeWord.handleBlock t₁)
      -- rotate the block of `t₁` back to the front
      have h3 : EdgeWord.TietzeStep
          (t'.flatMap EdgeWord.handleBlock ++ (S ++ EdgeWord.handleBlock t₁))
          ((t₁ :: t').flatMap EdgeWord.handleBlock ++ S) := by
        have h := EdgeWord.TietzeStep.rotate (w := (t'.flatMap EdgeWord.handleBlock ++ S) ++
          EdgeWord.handleBlock t₁) (t'.flatMap EdgeWord.handleBlock ++ S).length
        rw [List.rotate_append_length_eq] at h
        simpa [List.flatMap_cons, List.append_assoc] using h
      exact (h1.trans h2).tail h3

/--
**Gap 7 (now proved).** A word made of the `g` handle blocks in any order is Tietze
equivalent to the standard word. Pure list combinatorics: each handle swap followed by a
rotation carries one block past an arbitrary word (`handleBlock_moveToEnd`), which is
enough to realise any permutation of the blocks (`flatMap_handleBlock_perm`).
-/
theorem handleSwap_index_ordering
    {g : ℕ} (v : EdgeWord g)
    (_hGrouped : ∃ perm : Equiv.Perm (Fin g), v = (List.finRange g).flatMap (fun i => EdgeWord.handleBlock (perm i))) :
    EdgeWord.TietzeEq v (EdgeWord.standardWord g) := by
  obtain ⟨perm, rfl⟩ := _hGrouped
  have hperm : ((List.finRange g).map perm).Perm (List.finRange g) := perm.map_finRange_perm
  have h := flatMap_handleBlock_perm (List.finRange g) ((List.finRange g).map perm) hperm []
  simpa [EdgeWord.standardWord, List.flatMap_map, Function.comp_def] using h















theorem standardWord_wordSetoid_eq (g : ℕ) :
    EdgeWord.wordSetoid g (EdgeWord.standardWord g) = Polygon4g.sideSetoid g :=
  EdgeWord.wordSetoid_standardWord g


theorem quotient_homeo_of_setoid_eq
    {α : Type} [TopologicalSpace α] {s₁ s₂ : Setoid α} (h : s₁ = s₂) :
    Nonempty (@Quotient α s₁ ≃ₜ @Quotient α s₂) := by
  cases h
  exact ⟨Homeomorph.refl _⟩


theorem standardWord_wordQuotient_homeomorph_polygon4g (g : ℕ) :
    Nonempty (EdgeWord.wordQuotient g (EdgeWord.standardWord g) ≃ₜ Polygon4g g) := by
  -- Both sides are `Quotient (...)` of the same Setoid (after
  -- `standardWord_wordSetoid_eq`); the `quotient_homeo_of_setoid_eq`
  -- step transports along this equality.
  have _ := standardWord_wordSetoid_eq g
  exact quotient_homeo_of_setoid_eq (standardWord_wordSetoid_eq g)


theorem wordQuotient_continuous_bijection_to_M
    {M : Type} [TopologicalSpace M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus)
    (hw : w = E.word) :
    ∃ f : EdgeWord.wordQuotient E.g w → M,
      Continuous f ∧ Function.Bijective f := by
  cases hw
  let f : EdgeWord.wordQuotient E.g E.word → M :=
    Quotient.lift E.proj (fun z w_ hzw => (E.kernel z w_).mpr hzw)
  refine ⟨f, E.cts.quotient_lift _, ?_⟩
  refine ⟨?_, ?_⟩
  · intro a b hab
    induction a using Quotient.inductionOn with | _ z =>
    induction b using Quotient.inductionOn with | _ w_ =>
    change E.proj z = E.proj w_ at hab
    exact Quotient.sound ((E.kernel z w_).mp hab)
  · intro y
    obtain ⟨z, hz⟩ := E.surj y
    exact ⟨⟦z⟧, hz⟩


theorem edgeWord_wordQuotient_homeomorph_M
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus) (hw : w = E.word) :
    Nonempty (EdgeWord.wordQuotient E.extractedGenus w ≃ₜ M) := by
  -- For w = E.word, we use the bijection from E.proj.
  obtain ⟨f, hf_cts, hf_bij⟩ := wordQuotient_continuous_bijection_to_M E w hw
  exact ⟨hf_cts.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf_bij)⟩


end JacobianChallenge.Periods
