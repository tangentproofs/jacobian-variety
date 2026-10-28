/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/Periods/HandleSwapHomeo.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

/--
Disk tail-rotation homeomorphism: fixes the handle arcs and shifts the tail arcs.
This is the strictly narrower topological provider for `handlePrefix_tailRotate_homeomorph_nonzero`.
-/
private lemma tailRotate_geometric_maps
    {g : ℕ} (i : Fin g) (u : List (Letter g)) (m : ℕ) (_h_m : m ≠ 0) :
    ∃ (φ : DiskC ≃ₜ DiskC),
      ∀ x y, EdgeWord.sidePairingRel g ([Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i] ++ u) x y ↔
        EdgeWord.sidePairingRel g ([Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i] ++ u.rotate m) (φ x) (φ y) := by
  -- The geometric construction of the piecewise disk homeomorphism.
  sorry

/--
Nontrivial case of the tail-rotate homeomorphism: residual disk-geometry
content for `m ≠ 0`. Discharged by the tail-shift disk homeomorphism.
-/
theorem handlePrefix_tailRotate_homeomorph_nonzero
    {g : ℕ} (i : Fin g) (u : List (Letter g)) (m : ℕ) (_h_m : m ≠ 0) :
    Nonempty (EdgeWord.wordQuotient g
                ([Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i] ++ u) ≃ₜ
              EdgeWord.wordQuotient g
                ([Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i] ++ u.rotate m)) := by
  obtain ⟨φ, h_resp⟩ := tailRotate_geometric_maps i u m _h_m
  exact ⟨Quotient.homeo' φ h_resp⟩

/--
Rotating the tail of a handle-prefixed word preserves the quotient.
Dispatches on `m = 0` (handled by `handlePrefix_tailRotate_homeomorph_zero`)
vs `m ≠ 0` (handled by the residual `handlePrefix_tailRotate_homeomorph_nonzero`).
-/
theorem handlePrefix_tailRotate_homeomorph
    {g : ℕ} (i : Fin g) (u : List (Letter g)) (m : ℕ) :
    Nonempty (EdgeWord.wordQuotient g
                ([Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i] ++ u) ≃ₜ
              EdgeWord.wordQuotient g
                ([Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i] ++ u.rotate m)) := by
  by_cases h_m : m = 0
  · subst h_m
    exact handlePrefix_tailRotate_homeomorph_zero i u
  · exact handlePrefix_tailRotate_homeomorph_nonzero i u m h_m

/-- Handle swap = rotate + tail-rotate + rotate. -/
theorem wordQuotient_homeomorph_of_handleSwap_step_v2
    {g : ℕ} {w v : EdgeWord g} (hsw : HandleSwap w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  obtain ⟨i, xs, ys, _, rfl⟩ := hsw
  let hd := [Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i]
  obtain ⟨f1⟩ := wordQuotient_homeomorph_of_rotate (xs ++ hd ++ ys) xs.length
  have h1 : (xs ++ hd ++ ys).rotate xs.length = hd ++ (ys ++ xs) := by
    rw [List.append_assoc, rotate_app, List.append_assoc]
  rw [h1] at f1
  obtain ⟨f2⟩ := handlePrefix_tailRotate_homeomorph i (ys ++ xs) ys.length
  have h2 : (ys ++ xs).rotate ys.length = xs ++ ys := rotate_app ys xs
  rw [h2] at f2
  obtain ⟨f3⟩ := wordQuotient_homeomorph_of_rotate (hd ++ xs ++ ys) (hd.length + xs.length)
  have h3 : (hd ++ xs ++ ys).rotate (hd.length + xs.length) = ys ++ hd ++ xs := by
    rw [← List.length_append, rotate_app, List.append_assoc]
  rw [h3] at f3
  exact ⟨f1.trans (f2.trans f3)⟩
