import Jacobian.Periods.EdgeWord
import Mathlib.Logic.Relation

namespace JacobianChallenge.Periods

open EdgeWord Complex

instance hs_wq_topologicalSpace (g : ℕ) (w : EdgeWord g) :
    TopologicalSpace (EdgeWord.wordQuotient g w) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

instance hs_wq_compactSpace (g : ℕ) (w : EdgeWord g) :
    CompactSpace (EdgeWord.wordQuotient g w) :=
  inferInstanceAs (CompactSpace (Quotient _))

/-! ### Disk rotation infrastructure -/

lemma diskC_norm_le_one (z : DiskC) : ‖z.1‖ ≤ 1 := by
  have := z.2; rwa [Metric.mem_closedBall, dist_zero_right] at this

/-- Rotation of DiskC by complex multiplication. -/
noncomputable def diskMul (c : ℂ) (hc : ‖c‖ = 1) : DiskC ≃ₜ DiskC where
  toFun z := ⟨c * z, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, hc, one_mul]
    exact diskC_norm_le_one z⟩
  invFun z := ⟨c⁻¹ * z, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_inv, hc, inv_one, one_mul]
    exact diskC_norm_le_one z⟩
  left_inv z := by
    ext; simp only [← mul_assoc]
    have hne : c ≠ 0 := by intro h; simp [h] at hc
    rw [inv_mul_cancel₀ hne, one_mul]
  right_inv z := by
    ext; simp only [← mul_assoc]
    have hne : c ≠ 0 := by intro h; simp [h] at hc
    rw [mul_inv_cancel₀ hne, one_mul]
  continuous_toFun := Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _

lemma diskMul_apply (c : ℂ) (hc : ‖c‖ = 1) (z : DiskC) :
    (diskMul c hc z).val = c * z.1 := rfl

private lemma norm_exp_I_mul_real (r : ℝ) :
    ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

/--
Map a homeomorphism between two types to a homeomorphism between their quotients,
given that the homeomorphism respects the relations.
-/
private def Quotient.homeo' {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (f : α ≃ₜ β) {s₁ : Setoid α} {s₂ : Setoid β}
    (hf : ∀ x y, s₁.r x y ↔ s₂.r (f x) (f y)) :
    Quotient s₁ ≃ₜ Quotient s₂ where
  toFun := Quotient.map' f (fun x y h => (hf x y).mp h)
  invFun := Quotient.map' f.symm (fun x y h => by
    have h_symm := hf (f.symm x) (f.symm y)
    simp only [Homeomorph.apply_symm_apply] at h_symm
    rwa [h_symm])
  left_inv q := by induction q using Quotient.inductionOn'; simp
  right_inv q := by induction q using Quotient.inductionOn'; simp
  continuous_toFun := Continuous.quotient_map' f.continuous (fun x y h => (hf x y).mp h)
  continuous_invFun := Continuous.quotient_map' f.symm.continuous (fun x y h => by
    have h_symm := hf (f.symm x) (f.symm y); simp only [Homeomorph.apply_symm_apply] at h_symm; rwa [h_symm])

/-! ### Rotation-invariance lemmas -/

/-- Rigid rotation of the disk by a specified number of boundary sides. -/
noncomputable def diskRotateBySide (L : ℕ) (_hL : L ≠ 0) (k : ℕ) : DiskC ≃ₜ DiskC :=
  let theta := 2 * Real.pi * k / L
  diskMul (Complex.exp (Complex.I * theta)) (norm_exp_I_mul_real theta)

lemma diskRotateBySide_apply (L : ℕ) (_hL : L ≠ 0) (k : ℕ) (z : DiskC) :
    (diskRotateBySide L _hL k z).val = Complex.exp (Complex.I * (2 * Real.pi * k / L : ℝ)) * z.1 := rfl

private lemma exp_I_add_real (a b : ℝ) :
    Complex.exp (Complex.I * (a : ℂ)) *
      Complex.exp (Complex.I * (b : ℂ)) =
    Complex.exp (Complex.I * ((a + b : ℝ) : ℂ)) := by
  rw [← Complex.exp_add, ← mul_add]
  push_cast
  rfl

/-- **Narrow Leaf.** Rigid disk rotation transports boundary parameters. -/
lemma diskRotateBySide_boundaryParam
    (L : ℕ) (hL : L ≠ 0) (k i : ℕ) (t : ℝ) :
    diskRotateBySide L hL k (boundaryParam' L i t) =
    boundaryParam' L (i + k) t := by
  ext
  rw [diskRotateBySide_apply]
  simp only [boundaryParam', boundaryParamC', boundaryAngle']
  rw [mul_comm _ I, exp_I_add_real]
  push_cast
  congr 1
  field_simp [Nat.cast_ne_zero.mpr hL]
  ring

/-- **Narrow Leaf.** Side-pairing relation is preserved under rigid disk rotation. -/
private def shiftedFin (L : ℕ) (hL : L ≠ 0) (k : ℕ) (i : Fin L) : Fin L :=
  ⟨(i.val + k) % L, Nat.mod_lt _ (Nat.pos_of_ne_zero hL)⟩

private lemma boundaryParam'_mod_length
    (L : ℕ) (hL : L ≠ 0) (n : ℕ) (t : ℝ) :
    boundaryParam' L (n % L) t = boundaryParam' L n t := by
  ext
  simp only [boundaryParam', boundaryParamC', boundaryAngle']
  rw [Complex.exp_eq_exp_iff_exists_int]
  use - ((n / L : ℕ) : ℤ)
  rw [Int.cast_neg, Int.cast_natCast]
  have h_div_mod : ((n % L : ℕ) : ℝ) = (n : ℝ) - (L : ℝ) * ((n / L : ℕ) : ℝ) := by
    have h_id := Nat.mod_add_div n L
    have h_cast : ((n % L : ℕ) : ℝ) + (L : ℝ) * ((n / L : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast h_id
    rw [← h_cast]
    ring
  rw [h_div_mod]
  push_cast
  have hL_C : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  field_simp [hL_C]
  ring

private lemma boundaryParam'_shiftedFin
    (L : ℕ) (hL : L ≠ 0) (k : ℕ) (i : Fin L) (t : ℝ) :
    boundaryParam' L ((shiftedFin L hL k i).val) t =
      boundaryParam' L (i.val + k) t := by
  simp [shiftedFin]
  apply boundaryParam'_mod_length L hL

private lemma rotate_get_shiftedFin
    {α : Type*} (w : List α) (k : ℕ) (hL : w.length ≠ 0)
    (i : Fin (w.rotate k).length) :
    (w.rotate k).get i =
      w.get (shiftedFin w.length hL k
        ⟨i.val, by simpa [List.length_rotate] using i.is_lt⟩) := by
  rw [List.get_rotate]
  simp [shiftedFin]

private lemma sideGen_rotate_forward
    {g : ℕ} (w : EdgeWord g) (k : ℕ) (hL : w.length ≠ 0)
    {x y : DiskC} :
    EdgeWord.SideGen g (w.rotate k) x y →
      EdgeWord.SideGen g w
        (diskRotateBySide w.length hL k x)
        (diskRotateBySide w.length hL k y) := by
  intro h
  cases h with
  | pair i j t ht hletter =>
      let i' : Fin w.length := shiftedFin w.length hL k ⟨i.val, by simpa [List.length_rotate] using i.is_lt⟩
      let j' : Fin w.length := shiftedFin w.length hL k ⟨j.val, by simpa [List.length_rotate] using j.is_lt⟩
      have hL_rot : (w.rotate k).length = w.length := List.length_rotate w k
      have h1 : diskRotateBySide w.length hL k (boundaryParam' (w.rotate k).length i.val t) =
                 boundaryParam' w.length i'.val t := by
        rw [boundaryParam'_congr_length hL_rot, diskRotateBySide_boundaryParam, boundaryParam'_shiftedFin]
      have h2 : diskRotateBySide w.length hL k (boundaryParam' (w.rotate k).length j.val (1 - t)) =
                 boundaryParam' w.length j'.val (1 - t) := by
        rw [boundaryParam'_congr_length hL_rot, diskRotateBySide_boundaryParam, boundaryParam'_shiftedFin]
      rw [h1, h2]
      have hi_get : (w.rotate k).get i = w.get i' := rotate_get_shiftedFin w k hL i
      have hj_get : (w.rotate k).get j = w.get j' := rotate_get_shiftedFin w k hL j
      rw [hi_get, hj_get] at hletter
      apply EdgeWord.SideGen.pair i' j' t ht
      exact hletter

private lemma eqvGen_map
    {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    (f : α → β)
    (hrel : ∀ {x y}, r x y → s (f x) (f y)) :
    ∀ {x y}, Relation.EqvGen r x y → Relation.EqvGen s (f x) (f y) := by
  intro x y h
  induction h with
  | rel _ _ hr => exact Relation.EqvGen.rel _ _ (hrel hr)
  | refl x => exact Relation.EqvGen.refl (f x)
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

private lemma rotate_rotate_inv_length (L : ℕ) (hL : L ≠ 0) (k : ℕ) :
    (k + (L - k % L)) % L = 0 := by
  by_cases hk : k % L = 0
  · rw [hk, Nat.sub_zero]
    rw [Nat.add_mod, hk]
    simp [Nat.mod_self]
  · have h_lt : k % L < L := Nat.mod_lt k (Nat.pos_of_ne_zero hL)
    have hk_pos : k % L ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
    have h_sub_lt : L - k % L < L := by omega
    have h_sub_mod : (L - k % L) % L = L - k % L := Nat.mod_eq_of_lt h_sub_lt
    have h_eq : (k + (L - k % L)) % L = (k % L + (L - k % L)) % L := by
      rw [Nat.add_mod, h_sub_mod]
    rw [h_eq]
    have h_sub : k % L + (L - k % L) = L := by
      rw [Nat.add_comm]
      exact Nat.sub_add_cancel (le_of_lt h_lt)
    rw [h_sub]
    simp [Nat.mod_self]

private lemma diskRotateBySide_comp_inv (L : ℕ) (hL : L ≠ 0) (k : ℕ) (z : DiskC) :
    let kInv := L - k % L
    diskRotateBySide L hL kInv (diskRotateBySide L hL k z) = z := by
  dsimp only
  ext
  simp only [diskRotateBySide_apply]
  rw [← mul_assoc, exp_I_add_real]
  have h_exp_one : Complex.exp (Complex.I * ((2 * Real.pi * ((L - k % L : ℕ) : ℝ) / L + 2 * Real.pi * ((k : ℕ) : ℝ) / L : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_zero]
    rw [Complex.exp_eq_exp_iff_exists_int]
    use (((L - k % L + k) / L : ℕ) : ℤ)
    rw [Int.cast_natCast]
    have h_mod := rotate_rotate_inv_length L hL k
    rw [Nat.add_comm] at h_mod
    have h_div : L * (((L - k % L) + k) / L) = (L - k % L) + k := by
      apply Nat.mul_div_cancel'
      exact Nat.dvd_of_mod_eq_zero h_mod
    have h_cast_R : 2 * Real.pi * ((L - k % L : ℕ) : ℝ) / L + 2 * Real.pi * k / L =
                    2 * Real.pi * (L * (((L - k % L + k) / L : ℕ) : ℝ)) / L := by
      have hL_real : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL
      field_simp [hL_real]
      have h_lhs : ((L - k % L : ℕ) : ℝ) + (k : ℝ) = (((L - k % L) + k : ℕ) : ℝ) := by
        push_cast
        rfl
      have h_cast_nat : ((L - k % L : ℕ) : ℝ) + (k : ℝ) = L * (((L - k % L + k) / L : ℕ) : ℝ) := by
        rw [h_lhs]
        exact_mod_cast h_div.symm
      rw [← h_cast_nat]
    rw [h_cast_R]
    push_cast
    have hL_C : (L : ℂ) ≠ 0 := by exact_mod_cast hL
    field_simp [hL_C]
    ring
  rw [h_exp_one, one_mul]

theorem sidePairingRel_rotate_iff
    {g : ℕ} (w : EdgeWord g) (k : ℕ) (hL : w.length ≠ 0) :
    ∀ x y : DiskC,
      sidePairingRel g (w.rotate k) x y ↔
        sidePairingRel g w (diskRotateBySide w.length hL k x) (diskRotateBySide w.length hL k y) := by
  intro x y
  constructor
  · apply eqvGen_map (diskRotateBySide w.length hL k)
    intro a b hab
    apply sideGen_rotate_forward w k hL hab
  · intro h
    let k' := k % w.length
    let kInv := w.length - k'
    have h_w : (w.rotate k).rotate kInv = w := by
      rw [List.rotate_rotate, ← List.rotate_mod, rotate_rotate_inv_length w.length hL k, List.rotate_zero]
    have hL' : (w.rotate k).length ≠ 0 := by simpa using hL
    have h_back := eqvGen_map (diskRotateBySide w.length hL kInv) (by
      intro a b hab
      have hab' : SideGen g ((w.rotate k).rotate kInv) a b := by rwa [h_w]
      have h_gen := sideGen_rotate_forward (w.rotate k) kInv hL' hab'
      simp only [List.length_rotate] at h_gen
      exact h_gen) h
    rw [diskRotateBySide_comp_inv w.length hL k x, diskRotateBySide_comp_inv w.length hL k y] at h_back
    exact h_back

/-! ### Quotient lemmas -/

/-- Cyclic rotation of the word preserves the quotient. -/
theorem wordQuotient_homeomorph_of_rotate
    {g : ℕ} (w : EdgeWord g) (k : ℕ) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ
              EdgeWord.wordQuotient g (w.rotate k)) := by
  by_cases hL : w.length = 0
  · have hw : w = [] := List.eq_nil_of_length_eq_zero hL
    subst hw; exact ⟨Homeomorph.refl _⟩
  · let hL_pos : w.length ≠ 0 := hL
    let f := diskRotateBySide w.length hL_pos k
    have h_resp : ∀ x y, sidePairingRel g (w.rotate k) x y ↔ sidePairingRel g w (f x) (f y) := by
      intro x y; exact sidePairingRel_rotate_iff w k hL_pos x y
    exact ⟨(Quotient.homeo' f h_resp).symm⟩

/--
Base case of the tail-rotate homeomorphism: rotating by `m = 0` leaves
the tail unchanged, so the homeomorphism is the identity.
-/
theorem handlePrefix_tailRotate_homeomorph_zero
    {g : ℕ} (i : Fin g) (u : List (Letter g)) :
    Nonempty (EdgeWord.wordQuotient g
                ([Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i] ++ u) ≃ₜ
              EdgeWord.wordQuotient g
                ([Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i] ++ u.rotate 0)) := by
  rw [List.rotate_zero]
  exact ⟨Homeomorph.refl _⟩




/-! ### Assembly -/

private lemma rotate_app {α : Type*} (a b : List α) :
    (a ++ b).rotate a.length = b ++ a := by
  simp [List.rotate_eq_drop_append_take]


end JacobianChallenge.Periods
