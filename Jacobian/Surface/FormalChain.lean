import Jacobian.Surface.Pairing

/-!
# Formal chains of chart segments

A formal chain is a list of chart segments with orientations. For a formal chain `C`:

* `F C = ∏ E_s^{±1}`: smooth and non-vanishing off the vertices, with `∂̄(F C) = (F C) · θ C`
  (`F_local`), where `θ C = ∑ ± θ_s` is a smooth `(0,1)`-form;
* at every point `v`, `F C = (w - w₀)^{ord C v} · K` on a punctured neighbourhood, `K` smooth and
  non-vanishing at `w₀` (`F_vertex`); `ord C` is the boundary of `C`;
* `∫_X θ C ∧ ω = π ∫_C ω` (`integral_θ_mul`).
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff

/-- `∂̄` of `1/g`. -/
theorem dbar_inv {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g z) (h0 : g z ≠ 0) :
    dbar (fun w => (g w)⁻¹) z = -((g z)⁻¹ * (g z)⁻¹) * dbar g z := by
  have hinv : DifferentiableAt ℝ (fun w => (g w)⁻¹) z := hg.inv h0
  have hev : (fun w => g w * (g w)⁻¹) =ᶠ[𝓝 z] fun _ => (1 : ℂ) := by
    filter_upwards [hg.continuousAt.eventually_ne h0] with w hw using mul_inv_cancel₀ hw
  have h1 := dbar_mul hg hinv
  rw [dbar_eq_zero_of_eventuallyEq hev] at h1
  have h2 : g z * dbar (fun w => (g w)⁻¹) z = -((g z)⁻¹ * dbar g z) := by
    linear_combination -h1
  calc dbar (fun w => (g w)⁻¹) z = (g z)⁻¹ * (g z * dbar (fun w => (g w)⁻¹) z) := by
        rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]
    _ = _ := by rw [h2]; ring

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

variable (X) in
/-- A formal chain: chart segments with orientations (`true` = as given, `false` = reversed). -/
abbrev FChain := List (ChartSegment X × Bool)

namespace FChain

/-- The sign of an orientation. -/
def sgn (b : Bool) : ℤ := if b then 1 else -1

@[simp] theorem sgn_true : sgn true = 1 := rfl
@[simp] theorem sgn_false : sgn false = -1 := rfl

/-- The factor of one oriented segment. -/
noncomputable def fac (c : ChartSegment X × Bool) (x : X) : ℂ :=
  if c.2 then Seg.E c.1 x else (Seg.E c.1 x)⁻¹

/-- `∏ E_s^{±1}`. -/
noncomputable def F (C : FChain X) (x : X) : ℂ := (C.map fun c => fac c x).prod

/-- `∑ ± θ_s`. -/
noncomputable def θ (C : FChain X) : X → ℂ → ℂ := fun q w =>
  (C.map fun c => (sgn c.2 : ℂ) * Seg.θ c.1 q w).sum

/-- The boundary multiplicity at `v`. -/
noncomputable def ord (C : FChain X) (v : X) : ℤ := (C.map fun c => sgn c.2 * Seg.ord c.1 v).sum

/-- The vertices. -/
def V (C : FChain X) : Set X := {x | ∃ c ∈ C, x = c.1.start ∨ x = c.1.stop}

/-- The integral of a holomorphic form along `C`. -/
noncomputable def integral (C : FChain X) (η : HolomorphicOneForm ℂ X) : ℂ :=
  (C.map fun c => (sgn c.2 : ℂ) * c.1.integral η).sum

@[simp] theorem F_nil (x : X) : F ([] : FChain X) x = 1 := rfl
@[simp] theorem F_cons (c : ChartSegment X × Bool) (C : FChain X) (x : X) :
    F (c :: C) x = fac c x * F C x := by simp [F]
@[simp] theorem θ_nil (q : X) (w : ℂ) : θ ([] : FChain X) q w = 0 := rfl
@[simp] theorem θ_cons (c : ChartSegment X × Bool) (C : FChain X) (q : X) (w : ℂ) :
    θ (c :: C) q w = (sgn c.2 : ℂ) * Seg.θ c.1 q w + θ C q w := by simp [θ]
@[simp] theorem ord_nil (v : X) : ord ([] : FChain X) v = 0 := rfl
@[simp] theorem ord_cons (c : ChartSegment X × Bool) (C : FChain X) (v : X) :
    ord (c :: C) v = sgn c.2 * Seg.ord c.1 v + ord C v := by simp [ord]
@[simp] theorem integral_nil (η : HolomorphicOneForm ℂ X) : integral ([] : FChain X) η = 0 := rfl
@[simp] theorem integral_cons (c : ChartSegment X × Bool) (C : FChain X)
    (η : HolomorphicOneForm ℂ X) :
    integral (c :: C) η = (sgn c.2 : ℂ) * c.1.integral η + integral C η := by simp [integral]

theorem V_cons (c : ChartSegment X × Bool) (C : FChain X) :
    V (c :: C) = {c.1.start, c.1.stop} ∪ V C := by
  ext x
  simp only [V, List.mem_cons, mem_setOf_eq, mem_union, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨d, hd | hd, h⟩
    · subst hd; exact Or.inl h
    · exact Or.inr ⟨d, hd, h⟩
  · rintro (h | ⟨d, hd, h⟩)
    · exact ⟨c, Or.inl rfl, h⟩
    · exact ⟨d, Or.inr hd, h⟩

theorem V_finite (C : FChain X) : (V C).Finite := by
  induction C with
  | nil => simp [V]
  | cons c C ih => rw [V_cons]; exact (Set.toFinite _).union ih

theorem fac_ne_zero (c : ChartSegment X × Bool) (x : X) : fac c x ≠ 0 := by
  unfold fac; split_ifs
  · exact Seg.E_ne_zero _ _
  · exact inv_ne_zero (Seg.E_ne_zero _ _)

theorem F_ne_zero (C : FChain X) (x : X) : F C x ≠ 0 := by
  induction C with
  | nil => simp
  | cons c C ih => rw [F_cons]; exact mul_ne_zero (fac_ne_zero c x) ih

theorem θ_is01 (C : FChain X) : Is01 (θ C) := by
  induction C with
  | nil => intro p q w _; show (0 : ℂ) = _ * 0; rw [mul_zero]
  | cons c C ih =>
    intro p q w hw
    show (sgn c.2 : ℂ) * Seg.θ c.1 p w + θ C p w =
      _ * ((sgn c.2 : ℂ) * Seg.θ c.1 q _ + θ C q _)
    rw [Seg.θ_is01 c.1 p q w hw, ih p q w hw]
    ring

theorem smoothFam_θ (C : FChain X) : SmoothFam (θ C) := by
  induction C with
  | nil => intro p; exact contDiffOn_const
  | cons c C ih =>
    intro p
    exact (contDiffOn_const.mul (Seg.smoothFam_θ c.1 p)).add (ih p)

/-! ### Off the vertices -/

theorem fac_local (c : ChartSegment X × Bool) {q : X} {w : ℂ} (hw : w ∈ (chartAt ℂ q).target)
    (ha : (chartAt ℂ q).symm w ≠ c.1.start) (hb : (chartAt ℂ q).symm w ≠ c.1.stop) :
    ContDiffAt ℝ ∞ (rd (fac c) q) w ∧
      dbar (rd (fac c) q) w = rd (fac c) q w * ((sgn c.2 : ℂ) * Seg.θ c.1 q w) := by
  obtain ⟨h1, h2⟩ := Seg.E_local c.1 hw ha hb
  rcases c with ⟨s, _ | _⟩
  · have hrd : rd (fac (s, false)) q = fun v => (rd (Seg.E s) q v)⁻¹ := rfl
    have hne : rd (Seg.E s) q w ≠ 0 := Seg.E_ne_zero s _
    rw [hrd]
    refine ⟨h1.inv hne, ?_⟩
    rw [dbar_inv (h1.differentiableAt (by simp)) hne, h2]
    simp only [sgn_false]
    field_simp
    push_cast
    ring
  · have hrd : rd (fac (s, true)) q = rd (Seg.E s) q := rfl
    rw [hrd]
    refine ⟨h1, ?_⟩
    rw [h2]; simp

/-- **`F C` off the vertices.** -/
theorem F_local (C : FChain X) {q : X} {w : ℂ} (hw : w ∈ (chartAt ℂ q).target)
    (hV : (chartAt ℂ q).symm w ∉ V C) :
    ContDiffAt ℝ ∞ (rd (F C) q) w ∧ dbar (rd (F C) q) w = rd (F C) q w * θ C q w := by
  induction C with
  | nil =>
    have : rd (F ([] : FChain X)) q = fun _ => 1 := rfl
    rw [this]
    exact ⟨contDiffAt_const, by rw [dbar_eq_zero_of_eventuallyEq (c := 1) (by rfl)]; simp⟩
  | cons c C ih =>
    rw [V_cons] at hV
    simp only [mem_union, mem_insert_iff, mem_singleton_iff, not_or] at hV
    obtain ⟨⟨ha, hb⟩, hV⟩ := hV
    obtain ⟨h1, h2⟩ := fac_local c hw ha hb
    obtain ⟨h3, h4⟩ := ih hV
    have hrd : rd (F (c :: C)) q = fun v => rd (fac c) q v * rd (F C) q v := by
      funext v; simp [rd_apply]
    rw [hrd]
    refine ⟨h1.mul h3, ?_⟩
    rw [dbar_mul (h1.differentiableAt (by simp)) (h3.differentiableAt (by simp)), h2, h4,
      θ_cons]
    ring

/-! ### At the vertices -/

theorem fac_vertex (c : ChartSegment X × Bool) (v : X) :
    ∃ K : ℂ → ℂ, (∀ᶠ w in 𝓝 (chartAt ℂ v v), ContDiffAt ℝ ∞ K w) ∧
      K (chartAt ℂ v v) ≠ 0 ∧
      ∀ᶠ w in 𝓝[≠] (chartAt ℂ v v),
        rd (fac c) v w = (w - chartAt ℂ v v) ^ (sgn c.2 * Seg.ord c.1 v) * K w := by
  obtain ⟨K, hK, hK0, hev⟩ := Seg.E_vertex c.1 v
  rcases c with ⟨s, _ | _⟩
  · have hKne : ∀ᶠ w in 𝓝 (chartAt ℂ v v), K w ≠ 0 :=
      (hK.self_of_nhds.continuousAt).eventually_ne hK0
    refine ⟨fun w => (K w)⁻¹, ?_, inv_ne_zero hK0, ?_⟩
    · filter_upwards [hK, hKne] with w hw hw0 using hw.inv hw0
    · filter_upwards [hev] with w hw
      show (rd (Seg.E s) v w)⁻¹ = _
      rw [hw, mul_inv, sgn_false, neg_one_mul, zpow_neg]
  · refine ⟨K, hK, hK0, ?_⟩
    filter_upwards [hev] with w hw
    show rd (Seg.E s) v w = _
    rw [hw, sgn_true, one_mul]

/-- **`F C` at any point**: `(w - w₀)^{ord C v}` times a smooth non-vanishing factor. -/
theorem F_vertex (C : FChain X) (v : X) :
    ∃ K : ℂ → ℂ, (∀ᶠ w in 𝓝 (chartAt ℂ v v), ContDiffAt ℝ ∞ K w) ∧
      K (chartAt ℂ v v) ≠ 0 ∧
      ∀ᶠ w in 𝓝[≠] (chartAt ℂ v v),
        rd (F C) v w = (w - chartAt ℂ v v) ^ (ord C v) * K w := by
  induction C with
  | nil =>
    exact ⟨fun _ => 1, Eventually.of_forall fun _ => contDiffAt_const, one_ne_zero,
      Eventually.of_forall fun w => by simp [rd_apply]⟩
  | cons c C ih =>
    obtain ⟨K₁, hK₁, hK₁0, hev₁⟩ := fac_vertex c v
    obtain ⟨K₂, hK₂, hK₂0, hev₂⟩ := ih
    refine ⟨fun w => K₁ w * K₂ w, ?_, mul_ne_zero hK₁0 hK₂0, ?_⟩
    · filter_upwards [hK₁, hK₂] with w h1 h2 using h1.mul h2
    · filter_upwards [hev₁, hev₂, self_mem_nhdsWithin] with w h1 h2 hne
      have hw : w - chartAt ℂ v v ≠ 0 := sub_ne_zero.mpr hne
      show rd (F (c :: C)) v w = _
      rw [show rd (F (c :: C)) v w = rd (fac c) v w * rd (F C) v w by simp [rd_apply], h1, h2,
        ord_cons, zpow_add₀ hw]
      ring

/-! ### Chains, reversal, sums -/

/-- A chain, oriented forwards. -/
def fwd (l : List (ChartSegment X)) : FChain X := l.map fun s => (s, true)

/-- Reversal of orientation. -/
def neg (C : FChain X) : FChain X := C.map fun c => (c.1, !c.2)

theorem ord_append (C D : FChain X) (v : X) : ord (C ++ D) v = ord C v + ord D v := by
  simp [ord]

theorem ord_neg (C : FChain X) (v : X) : ord (neg C) v = -ord C v := by
  induction C with
  | nil => simp [neg]
  | cons c C ih =>
    have : neg (c :: C) = (c.1, !c.2) :: neg C := rfl
    rw [this, ord_cons, ord_cons, ih]
    rcases c with ⟨s, _ | _⟩ <;> simp [sgn] <;> ring

theorem integral_append (C D : FChain X) (η : HolomorphicOneForm ℂ X) :
    integral (C ++ D) η = integral C η + integral D η := by
  simp [integral]

theorem integral_neg (C : FChain X) (η : HolomorphicOneForm ℂ X) :
    integral (neg C) η = -integral C η := by
  induction C with
  | nil => simp [neg]
  | cons c C ih =>
    have : neg (c :: C) = (c.1, !c.2) :: neg C := rfl
    rw [this, integral_cons, integral_cons, ih]
    rcases c with ⟨s, _ | _⟩ <;> simp [sgn] <;> ring

theorem integral_fwd (l : List (ChartSegment X)) (η : HolomorphicOneForm ℂ X) :
    integral (fwd l) η = chainIntegral η l := by
  induction l with
  | nil => simp [fwd]
  | cons s l ih =>
    have : fwd (s :: l) = (s, true) :: fwd l := rfl
    rw [this, integral_cons, ih, chainIntegral_cons]
    simp

open Classical in
/-- The boundary of a chain from `P` to `Q` is `Q - P`. -/
theorem ord_fwd {l : List (ChartSegment X)} {P Q : X} (hl : IsChain l P Q) (v : X) :
    ord (fwd l) v = (if v = Q then 1 else 0) - (if v = P then 1 else 0) := by
  induction l generalizing P with
  | nil =>
    simp only [isChain_nil] at hl
    subst hl
    simp [fwd]
  | cons s l ih =>
    obtain ⟨h1, h2⟩ := hl
    have : fwd (s :: l) = (s, true) :: fwd l := rfl
    rw [this, ord_cons, ih h2, sgn_true, one_mul, Seg.ord, ← h1]
    ring

/-- Linearity of the chain integral. -/
theorem integral_add_form (C : FChain X) (η₁ η₂ : HolomorphicOneForm ℂ X) :
    integral C (η₁ + η₂) = integral C η₁ + integral C η₂ := by
  induction C with
  | nil => simp
  | cons c C ih => simp only [integral_cons, ih, ChartSegment.integral_add]; ring

theorem integral_smul_form (C : FChain X) (a : ℂ) (η : HolomorphicOneForm ℂ X) :
    integral C (a • η) = a * integral C η := by
  induction C with
  | nil => simp
  | cons c C ih => simp only [integral_cons, ih, ChartSegment.integral_smul, smul_eq_mul]; ring

/-- The chain integral as a linear functional. -/
noncomputable def integralLM (C : FChain X) : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ where
  toFun := integral C
  map_add' := integral_add_form C
  map_smul' := integral_smul_form C

/-! ### The pairing -/

/-- `∫_X (θ C) · ω = π ∫_C ω`, in an atlas containing the charts of all segments. -/
theorem integral_θ_mul (A : DiscAtlas X) (C : FChain X)
    (hA : ∀ c ∈ C, ∃ k, A.p k = c.1.p) (η : HolomorphicOneForm ℂ X) :
    A.integral (fun q w => θ C q w * holoF η q w) = (Real.pi : ℂ) * integral C η := by
  induction C with
  | nil =>
    simp only [θ_nil, zero_mul, integral_nil, mul_zero]
    simp [DiscAtlas.integral]
  | cons c C ih =>
    obtain ⟨k, hk⟩ := hA c (List.mem_cons_self ..)
    have hc1 : ∀ q, ContinuousOn (fun w => (sgn c.2 : ℂ) * Seg.θ c.1 q w * holoF η q w)
        (chartAt ℂ q).target := fun q =>
      (continuousOn_const.mul (Seg.smoothFam_θ c.1 q).continuousOn).mul
        (smoothFam_holoF η q).continuousOn
    have hc2 : ∀ q, ContinuousOn (fun w => θ C q w * holoF η q w) (chartAt ℂ q).target :=
      fun q => (smoothFam_θ C q).continuousOn.mul (smoothFam_holoF η q).continuousOn
    have e : A.integral (fun q w => θ (c :: C) q w * holoF η q w) =
        A.integral (fun q w => (sgn c.2 : ℂ) * Seg.θ c.1 q w * holoF η q w) +
          A.integral (fun q w => θ C q w * holoF η q w) := by
      rw [← A.integral_add' hc1 hc2]
      refine A.integral_congr fun i w _ => ?_
      simp only [θ_cons]; ring
    have e2 : A.integral (fun q w => (sgn c.2 : ℂ) * Seg.θ c.1 q w * holoF η q w) =
        (sgn c.2 : ℂ) * A.integral (fun q w => Seg.θ c.1 q w * holoF η q w) := by
      unfold DiscAtlas.integral
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← MeasureTheory.integral_const_mul]
      congr 1; funext w; ring
    rw [e, e2, Seg.integral_θ_mul c.1 A k hk, ih fun d hd => hA d (List.mem_cons_of_mem _ hd),
      integral_cons]
    ring

end FChain

end JacobianChallenge.Surface
