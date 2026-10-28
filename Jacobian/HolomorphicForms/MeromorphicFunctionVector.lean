import Jacobian.HolomorphicForms.MeromorphicFunction
import Jacobian.HolomorphicForms.VanishingOrder
import Jacobian.HolomorphicForms.Divisor
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Meromorphic functions and the divisor-facing replacement API

`MeromorphicFunctionType X` is the project's current raw representation of a
meromorphic function: a continuous map `X → OnePoint ℂ` whose finite projection
is locally meromorphic.  This representation is useful for single functions,
but it is **not** a sound model for the vector space of meromorphic germs.

The old pointwise addition on `OnePoint ℂ` sent any summand equal to `∞` to
`∞`.  That loses pole cancellation: two meromorphic functions with opposite
principal parts can sum to a finite holomorphic value, but the pointwise
`OnePoint` rule still returns `∞`.  Consequently this file deliberately does
not export `AddCommGroup` or `Module ℂ` instances for
`MeromorphicFunctionType X`.

The replacement API below is `MeromorphicFunctionWithDivisors`.  It bundles the
raw map with zero, pole, and principal divisors plus the compatibility facts
needed by downstream arguments.  Algebraic constructions on this bundled type
must provide divisor-side specifications explicitly; until germ-level
addition is available, users should state conditional lemmas with those
compatibility hypotheses rather than relying on global algebraic instances.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold OnePoint
open JacobianChallenge.HolomorphicForms.VanishingOrder

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

namespace MeromorphicFunctionType

/--
Structural axiom (S1a). When the pole divisor is 0, the map
f.toMap never takes the value ∞.
-/
def is_holomorphic (f : MeromorphicFunctionType X) : Prop :=
  ∀ x, f.toFun x ≠ ∞

/-- If f is holomorphic, we can project it to ℂ. -/
def toFiniteFun (f : MeromorphicFunctionType X) : X → ℂ :=
  fun x => (f.toFun x).getD 0

/-- The zero meromorphic function. -/
def zero (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    MeromorphicFunctionType X :=
  { toFun := fun _ => (0 : ℂ)
    toFun_continuous := continuous_const
    isMeromorphic := fun p => by
      unfold MeromorphicAtX
      show MeromorphicAt ((fun _ => (0 : ℂ)) ∘ (extChartAt 𝓘(ℂ) p).symm) (extChartAt 𝓘(ℂ) p p)
      exact AnalyticAt.meromorphicAt analyticAt_const }

instance : Zero (MeromorphicFunctionType X) := ⟨zero X⟩

/-!
The former `add_meromorphic` operation has been removed from the exported API.
Pointwise addition on `OnePoint ℂ` is not meromorphic-function addition because
it cannot cancel principal parts at poles.  A future operation must either work
on germs/quotients or return a bundled value together with divisor
compatibility data.
-/

/-- Negation of meromorphic functions. -/
noncomputable def neg_meromorphic (f : MeromorphicFunctionType X) : MeromorphicFunctionType X :=
  { toFun := fun x => OnePoint.map (fun c => -c) (f.toFun x)
    toFun_continuous := by
      exact (OnePoint.continuous_map continuous_neg
        (Homeomorph.neg ℂ).map_coclosedCompact.le).comp f.toFun_continuous
    isMeromorphic := by
      intro p
      unfold MeromorphicAtX
      have hf := f.isMeromorphic p
      convert hf.neg using 1
      ext z
      cases h : f.toFun ((chartAt ℂ p).symm z) <;> simp [h, Option.getD] }

noncomputable instance : Neg (MeromorphicFunctionType X) := ⟨neg_meromorphic⟩

/-- The toFun of a negation is the pointwise negation. -/
theorem neg_toFun {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) :
    ∀ x, f.toFun x ≠ ∞ → (-f).toFun x = (-(f.toFun x).getD 0 : ℂ) := by
  intro x hx
  show (neg_meromorphic f).toFun x = ↑(-(f.toFun x).getD 0)
  simp only [neg_meromorphic]
  cases h : f.toFun x with
  | infty => exact absurd h hx
  | coe c =>
    simp only [OnePoint.map, Option.getD]
    rfl

/-- Scalar multiplication of meromorphic functions. -/
noncomputable def smul_meromorphic (c : ℂ) (f : MeromorphicFunctionType X) : MeromorphicFunctionType X :=
  if hc : c = 0 then 0 else
  { toFun := fun x => OnePoint.map (c * ·) (f.toFun x)
    toFun_continuous := by
      have hcont : Continuous (fun z : ℂ => c * z) := continuous_const.mul continuous_id
      exact (OnePoint.continuous_map hcont
        ((Homeomorph.mulLeft₀ c hc).map_coclosedCompact.le)).comp f.toFun_continuous
    isMeromorphic := by
      intro p
      unfold MeromorphicAtX
      have hf := f.isMeromorphic p
      have hm : MeromorphicAt
          (fun z => c * f.toFiniteFun ((chartAt ℂ p).symm z))
          (chartAt ℂ p p) := by
        have hmul := (MeromorphicAt.const c (chartAt ℂ p p)).mul hf
        exact hmul.congr (Filter.Eventually.of_forall fun _ => rfl)
      convert hm using 1
      ext z
      cases h : f.toFun ((chartAt ℂ p).symm z) <;>
        simp +decide [extChartAt, MeromorphicFunctionType.toFiniteFun, h, Option.getD] }

noncomputable instance : SMul ℂ (MeromorphicFunctionType X) := ⟨smul_meromorphic⟩

/-- The toFun of a scalar multiplication is the pointwise multiplication. -/
theorem smul_toFun {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (c : ℂ) (f : MeromorphicFunctionType X) :
    ∀ x, f.toFun x ≠ ∞ → (c • f).toFun x = (c * (f.toFun x).getD 0 : ℂ) := by
  intro x hx
  show (smul_meromorphic c f).toFun x = ↑(c * Option.getD (f.toFun x) 0)
  by_cases hc : c = 0
  · rw [smul_meromorphic, dif_pos hc]
    change (zero X).toFun x = ↑(c * Option.getD (f.toFun x) 0)
    simp [zero, hc]
  · simp only [smul_meromorphic, dif_neg hc]
    cases h : f.toFun x with
    | infty => exact absurd h hx
    | coe z => rfl

/-- Constant meromorphic functions. -/
def constant (c : ℂ) : MeromorphicFunctionType X :=
  { toFun := fun _ => (c : OnePoint ℂ)
    toFun_continuous := continuous_const
    isMeromorphic := fun p => by
      unfold MeromorphicAtX
      show MeromorphicAt ((fun _ => c) ∘ (extChartAt 𝓘(ℂ) p).symm) (extChartAt 𝓘(ℂ) p p)
      exact AnalyticAt.meromorphicAt analyticAt_const }

/--
The old global vector-space instance is intentionally unavailable.

Pole cancellation cannot be represented by pointwise arithmetic on
`OnePoint ℂ`; use `MeromorphicFunctionWithDivisors` or a future germ quotient
instead.
-/
theorem meromorphicFunctionVectorSpace_blocked {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    True :=
  trivial

/-- Coefficient of the zero divisor at a point. -/
noncomputable def zeros_coeff {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (p : X) : ℤ :=
  haveI := Classical.propDecidable (f.toFun p = (0 : ℂ))
  if f.toFun p = (0 : ℂ) then (orderAt p (fun q => (f q).getD 0)).untopD 0 else 0

/-- Coefficient of the pole divisor at a point. -/
noncomputable def poles_coeff {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (p : X) : ℤ :=
  haveI := Classical.propDecidable (f.toFun p = ∞)
  if f.toFun p = ∞ then -(orderAt p (fun q => (f q).getD 0)).untopD 0 else 0

/--
This carries no analytic content; use `MeromorphicFunctionWithDivisors.zeros`
for divisor-sensitive statements.
-/
noncomputable def zeros {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_f : MeromorphicFunctionType X) : Divisor X :=
  0

/--
This definition intentionally carries no analytic content.  A raw
`MeromorphicFunctionType` does not include the finite-support and compatibility
data needed to recover a pole divisor soundly.  Use
`MeromorphicFunctionWithDivisors.poles` when divisor information matters.
-/
noncomputable def poles {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_f : MeromorphicFunctionType X) : Divisor X :=
  0

/-- The principal divisor `(f) = (zeros) - (poles)`. -/
noncomputable def principal {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) : Divisor X :=
  f.zeros - f.poles

/-!
Use `toFun_ne_infty_of_is_holomorphic` for raw functions, or use
`MeromorphicFunctionWithDivisors.toFun_ne_infty_of_poles_eq_zero` when the pole
divisor is bundled with compatibility data.
-/

/--
Sound replacement for the old false `poles = 0` bridge on raw functions:
the needed hypothesis is exactly that the raw map has no infinite values.
-/
theorem toFun_ne_infty_of_is_holomorphic {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (h : f.is_holomorphic) :
    ∀ x, f.toFun x ≠ ∞ :=
  h

/-- At a finite point of `OnePoint ℂ`, the finite-value projection is continuous. -/
private lemma finiteProjection_continuousAt (c : ℂ) :
    ContinuousAt (fun y : OnePoint ℂ => y.getD 0) (c : OnePoint ℂ) := by
  rw [OnePoint.continuousAt_coe]
  have hid : ContinuousAt (id : ℂ → ℂ) c := continuousAt_id
  exact hid.congr (Filter.Eventually.of_forall fun _ => rfl)

/-- If a meromorphic function has no infinite values, its finite projection is continuous. -/
private lemma toFiniteFun_continuousAt (f : MeromorphicFunctionType X)
    (h : ∀ x, f.toFun x ≠ ∞) (p : X) : ContinuousAt f.toFiniteFun p := by
  unfold MeromorphicFunctionType.toFiniteFun
  cases hp : f.toFun p with
  | infty => exact False.elim ((h p) hp)
  | coe c =>
      have hg : ContinuousAt (fun y : OnePoint ℂ => y.getD 0) (f.toFun p) := by
        simpa [hp] using finiteProjection_continuousAt c
      have hf : ContinuousAt f.toFun p := f.toFun_continuous.continuousAt
      exact hg.comp hf

/--
Structural bridge: if `f.toFun` never takes the value `∞`, then
`f.toFiniteFun` is `MDifferentiable`.
-/
theorem mdifferentiable_toFiniteFun_of_no_infty {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (h : ∀ x, f.toFun x ≠ ∞) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f.toFiniteFun :=
  fun p => by
    rw [mdifferentiableAt_iff]
    constructor
    · exact toFiniteFun_continuousAt f h p
    · have hs : ContinuousAt (fun z => (extChartAt 𝓘(ℂ) p).symm z)
          (extChartAt 𝓘(ℂ) p p) := by
        exact continuousAt_extChartAt_symm p
      have hsymm : (extChartAt 𝓘(ℂ) p).symm (extChartAt 𝓘(ℂ) p p) = p := by
        simp [extChartAt]
      have hcont_at_symm : ContinuousAt f.toFiniteFun
          ((extChartAt 𝓘(ℂ) p).symm (extChartAt 𝓘(ℂ) p p)) := by
        simpa [hsymm] using toFiniteFun_continuousAt f h p
      have hcont_chart : ContinuousAt
          (fun z => f.toFiniteFun ((extChartAt 𝓘(ℂ) p).symm z))
          (extChartAt 𝓘(ℂ) p p) := by
        exact hcont_at_symm.comp hs
      have han : AnalyticAt ℂ
          (fun z => f.toFiniteFun ((extChartAt 𝓘(ℂ) p).symm z))
          (extChartAt 𝓘(ℂ) p p) := by
        exact (f.isMeromorphic p).analyticAt hcont_chart
      have hd : DifferentiableAt ℂ
          (fun z => f.toFiniteFun ((extChartAt 𝓘(ℂ) p).symm z))
          (extChartAt 𝓘(ℂ) p p) := han.differentiableAt
      simpa [writtenInExtChartAt, Function.comp_def] using hd.differentiableWithinAt

/-- Constant meromorphic functions have no poles. -/
theorem constant_poles {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (c : ℂ) : (constant (X := X) c).poles = 0 :=
  by
    ext p
    simp [poles]

/-- Non-zero constant meromorphic functions have no zeros. -/
theorem constant_zeros {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (c : ℂ) (_hc : c ≠ 0) : (constant (X := X) c).zeros = 0 :=
  by
    ext p
    simp [zeros]

/-- Membership in the Riemann-Roch space `L(D)`: `f = 0` or `(f) + D ≥ 0`. -/
def MemRiemannRochSpace {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (D : Divisor X) : Prop :=
  f = 0 ∨ Divisor.Effective (f.principal + D)

end MeromorphicFunctionType

/-- The punctured-neighborhood filter at a point of `X`. -/
abbrev puncturedNhds (p : X) : Filter X :=
  nhdsWithin p {p}ᶜ

/--
A local meromorphic germ at `p`.

This is the first genuinely additive layer in the repair: arithmetic is
performed in Mathlib's `Filter.Germ`, where representatives are identified up
to eventual equality on a punctured neighborhood.  This is the local mechanism
needed for pole cancellation.
-/
@[ext] structure MeromorphicGermAt
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
 (p : X) where
  germ : Filter.Germ (puncturedNhds p) ℂ
  meromorphic :
    ∃ f : X → ℂ, germ = (f : Filter.Germ (puncturedNhds p) ℂ) ∧ MeromorphicAtX f p

namespace MeromorphicGermAt

variable {p : X}

instance : Coe (MeromorphicGermAt X p) (Filter.Germ (puncturedNhds p) ℂ) :=
  ⟨MeromorphicGermAt.germ⟩

/-- Constant local meromorphic germ. -/
def constant (c : ℂ) : MeromorphicGermAt X p :=
  { germ := c
    meromorphic := by
      refine ⟨fun _ => c, ?_, ?_⟩
      · rfl
      · unfold MeromorphicAtX
        show MeromorphicAt ((fun _ => c) ∘ (extChartAt 𝓘(ℂ) p).symm)
          (extChartAt 𝓘(ℂ) p p)
        exact AnalyticAt.meromorphicAt analyticAt_const }

/-- The zero local meromorphic germ. -/
def zero : MeromorphicGermAt X p :=
  constant 0

instance : Zero (MeromorphicGermAt X p) := ⟨zero⟩

/--
Addition of local meromorphic germs.  This is well-defined because
`Filter.Germ` quotients representatives by eventual equality.
-/
def add (F G : MeromorphicGermAt X p) : MeromorphicGermAt X p :=
  { germ := F.germ + G.germ
    meromorphic := by
      rcases F.meromorphic with ⟨f, hf_eq, hf_mer⟩
      rcases G.meromorphic with ⟨g, hg_eq, hg_mer⟩
      refine ⟨f + g, ?_, hf_mer.add hg_mer⟩
      rw [hf_eq, hg_eq]
      rfl }

instance : Add (MeromorphicGermAt X p) := ⟨add⟩

/-- Negation of a local meromorphic germ. -/
def neg (F : MeromorphicGermAt X p) : MeromorphicGermAt X p :=
  { germ := -F.germ
    meromorphic := by
      rcases F.meromorphic with ⟨f, hf_eq, hf_mer⟩
      refine ⟨-f, ?_, hf_mer.neg⟩
      rw [hf_eq]
      rfl }

instance : Neg (MeromorphicGermAt X p) := ⟨neg⟩

/-- Scalar multiplication of a local meromorphic germ. -/
def smul (c : ℂ) (F : MeromorphicGermAt X p) : MeromorphicGermAt X p :=
  { germ := c • F.germ
    meromorphic := by
      rcases F.meromorphic with ⟨f, hf_eq, hf_mer⟩
      refine ⟨c • f, ?_, ?_⟩
      · rw [hf_eq]
        rfl
      · have hmul := (MeromorphicAt.const c (extChartAt 𝓘(ℂ) p p)).mul hf_mer
        exact hmul.congr (Filter.Eventually.of_forall fun _ => rfl) }

instance : SMul ℂ (MeromorphicGermAt X p) := ⟨smul⟩

@[simp] theorem zero_germ : (0 : MeromorphicGermAt X p).germ = 0 := rfl
@[simp] theorem constant_germ (c : ℂ) : (constant (X := X) (p := p) c).germ = c := rfl
@[simp] theorem add_germ (F G : MeromorphicGermAt X p) :
    (F + G).germ = F.germ + G.germ := rfl
@[simp] theorem neg_germ (F : MeromorphicGermAt X p) :
    (-F).germ = -F.germ := rfl
@[simp] theorem smul_germ (c : ℂ) (F : MeromorphicGermAt X p) :
    (c • F).germ = c • F.germ := rfl

noncomputable instance : AddCommGroup (MeromorphicGermAt X p) where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc F G H := by ext; simp [add_assoc]
  zero_add F := by ext; simp
  add_zero F := by ext; simp
  add_comm F G := by ext; simp [add_comm]
  neg_add_cancel F := by ext; simp

noncomputable instance : Module ℂ (MeromorphicGermAt X p) where
  smul := (· • ·)
  one_smul F := by ext; simp
  mul_smul c d F := by ext; simp [mul_smul]
  smul_zero c := by ext; simp
  smul_add c F G := by ext; simp [smul_add]
  add_smul c d F := by ext; simp [add_smul]
  zero_smul F := by ext; simp

end MeromorphicGermAt

/-- A global meromorphic object represented by its local germs at every point. -/
abbrev MeromorphicGermFamily
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : Type _ :=
  ∀ p : X, MeromorphicGermAt X p

namespace MeromorphicGermFamily

/-- Evaluation of a global germ family at a point. -/
def germAt (F : MeromorphicGermFamily X) (p : X) : MeromorphicGermAt X p :=
  F p

/--
The germ-family vector-space instance is available because each local
germ space is a genuine `ℂ`-module.
-/
theorem module_nonempty :
    Nonempty (Module ℂ (MeromorphicGermFamily X)) :=
  ⟨inferInstance⟩

@[simp] theorem add_germAt (F G : MeromorphicGermFamily X) (p : X) :
    germAt (F + G) p = germAt F p + germAt G p :=
  rfl

@[simp] theorem smul_germAt (c : ℂ) (F : MeromorphicGermFamily X) (p : X) :
    germAt (c • F) p = c • germAt F p :=
  rfl

@[simp] theorem neg_germAt (F : MeromorphicGermFamily X) (p : X) :
    germAt (-F) p = -germAt F p :=
  rfl

end MeromorphicGermFamily

namespace MeromorphicFunctionType

/-- The punctured local finite-value germ of a raw meromorphic function. -/
def germAt (f : MeromorphicFunctionType X) (p : X) : MeromorphicGermAt X p :=
  { germ := (f.toFiniteFun : Filter.Germ (puncturedNhds p) ℂ)
    meromorphic := ⟨f.toFiniteFun, rfl, f.isMeromorphic p⟩ }

/--
The global family of punctured local finite-value germs attached to a raw
meromorphic function.
-/
def germFamily (f : MeromorphicFunctionType X) : MeromorphicGermFamily X :=
  fun p => f.germAt p

@[simp] theorem germAt_germ (f : MeromorphicFunctionType X) (p : X) :
    (f.germAt p).germ = (f.toFiniteFun : Filter.Germ (puncturedNhds p) ℂ) :=
  rfl

end MeromorphicFunctionType

/--
Coefficient of the zero divisor extracted from an order value.

The `⊤` case is sent to `0`; global zero functions need separate handling in
the eventual full divisor theory.
-/
noncomputable def zeroCoeffOfOrder (o : WithTop ℤ) : ℤ :=
  max (o.untopD 0) 0

/-- Coefficient of the pole divisor extracted from an order value. -/
noncomputable def poleCoeffOfOrder (o : WithTop ℤ) : ℤ :=
  max (-(o.untopD 0)) 0

/-- Coefficient of the principal divisor extracted from an order value. -/
noncomputable def principalCoeffOfOrder (o : WithTop ℤ) : ℤ :=
  o.untopD 0

/--
Divisor-compatible replacement for the raw `MeromorphicFunctionType`.

This structure is intentionally not given global algebraic instances.  Any
addition, multiplication, or scalar action that changes the divisor data must
construct a new value and prove the relevant compatibility fields.
-/
structure MeromorphicFunctionWithDivisors
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  toFunction : MeromorphicFunctionType X
  /--
Local meromorphic germs.  These are the additive data; unlike
  pointwise `OnePoint` values, they can model pole cancellation.
-/
  germs : MeromorphicGermFamily X
  /--
The local germs agree with the finite-value germ family attached to the
  raw `OnePoint`-valued map.
-/
  germs_eq_toFunction : germs = toFunction.germFamily
  zeroDivisor : Divisor X
  poleDivisor : Divisor X
  principalDivisor : Divisor X
  /--
Recorded local order data.  A full germ-order bridge should eventually
  prove this is the order of `germs P`; for now the divisor API requires all
  divisor fields to agree with this order function.
-/
  order : X → WithTop ℤ
  zeroDivisor_apply : ∀ P : X, zeroDivisor P = zeroCoeffOfOrder (order P)
  poleDivisor_apply : ∀ P : X, poleDivisor P = poleCoeffOfOrder (order P)
  principalDivisor_apply : ∀ P : X, principalDivisor P = principalCoeffOfOrder (order P)
  principalDivisor_eq : principalDivisor = zeroDivisor - poleDivisor
  poleDivisor_nonneg : ∀ P : X, 0 ≤ poleDivisor P
  zero_or_pole_eq_zero : ∀ P : X, zeroDivisor P = 0 ∨ poleDivisor P = 0
  toFun_ne_infty_of_poleDivisor_zero :
    ∀ P : X, poleDivisor P = 0 → toFunction.toFun P ≠ (OnePoint.infty : OnePoint ℂ)

namespace MeromorphicFunctionWithDivisors

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

instance : CoeFun (MeromorphicFunctionWithDivisors X) (fun _ => X → OnePoint ℂ) where
  coe f := f.toFunction.toFun

/-- The zero divisor of a divisor-compatible meromorphic function. -/
def zeros (f : MeromorphicFunctionWithDivisors X) : Divisor X :=
  f.zeroDivisor

/-- The pole divisor of a divisor-compatible meromorphic function. -/
def poles (f : MeromorphicFunctionWithDivisors X) : Divisor X :=
  f.poleDivisor

/-- The principal divisor `(f)`, recorded as zero divisor minus pole divisor. -/
def principal (f : MeromorphicFunctionWithDivisors X) : Divisor X :=
  f.principalDivisor

@[simp] theorem principal_eq_zeroDivisor_sub_poleDivisor
    (f : MeromorphicFunctionWithDivisors X) :
    f.principal = f.zeros - f.poles :=
  f.principalDivisor_eq

/-- Sound no-poles bridge for the divisor-compatible API. -/
theorem toFun_ne_infty_of_poles_eq_zero
    (f : MeromorphicFunctionWithDivisors X) (h : f.poles = 0) :
    ∀ P, f.toFunction.toFun P ≠ (OnePoint.infty : OnePoint ℂ) := by
  intro P
  exact f.toFun_ne_infty_of_poleDivisor_zero P (by
    change f.poles P = 0
    rw [h]
    rfl)

/-- Membership in `L(D)` for the divisor-compatible API. -/
def MemRiemannRochSpace (f : MeromorphicFunctionWithDivisors X) (D : Divisor X) : Prop :=
  Divisor.Effective (f.principal + D)

@[simp] theorem zeros_apply (f : MeromorphicFunctionWithDivisors X) (P : X) :
    f.zeros P = zeroCoeffOfOrder (f.order P) :=
  f.zeroDivisor_apply P

@[simp] theorem poles_apply (f : MeromorphicFunctionWithDivisors X) (P : X) :
    f.poles P = poleCoeffOfOrder (f.order P) :=
  f.poleDivisor_apply P

@[simp] theorem principal_apply (f : MeromorphicFunctionWithDivisors X) (P : X) :
    f.principal P = principalCoeffOfOrder (f.order P) :=
  f.principalDivisor_apply P

/--
A nonzero constant as a divisor-compatible meromorphic function.

The zero constant is deliberately not provided by this constructor: its zero
divisor is not a finite divisor in the usual principal-divisor convention.
-/
def constantNonzero (c : ℂ) (_hc : c ≠ 0) : MeromorphicFunctionWithDivisors X :=
  { toFunction := MeromorphicFunctionType.constant c
    germs := fun P => MeromorphicGermAt.constant (X := X) (p := P) c
    germs_eq_toFunction := by
      funext P
      ext
      apply Filter.EventuallyEq.germ_eq
      filter_upwards with Q
      rfl
    zeroDivisor := 0
    poleDivisor := 0
    principalDivisor := 0
    order := fun _ => (0 : WithTop ℤ)
    zeroDivisor_apply := by intro P; simp [zeroCoeffOfOrder]
    poleDivisor_apply := by intro P; simp [poleCoeffOfOrder]
    principalDivisor_apply := by intro P; simp [principalCoeffOfOrder]
    principalDivisor_eq := by simp
    poleDivisor_nonneg := by intro P; simp
    zero_or_pole_eq_zero := by intro P; exact Or.inl (by simp)
    toFun_ne_infty_of_poleDivisor_zero := by
      intro P _hP
      simp [MeromorphicFunctionType.constant] }

@[simp] theorem constantNonzero_poles (c : ℂ) (hc : c ≠ 0) :
    (constantNonzero (X := X) c hc).poles = 0 :=
  rfl

@[simp] theorem constantNonzero_principal (c : ℂ) (hc : c ≠ 0) :
    (constantNonzero (X := X) c hc).principal = 0 :=
  rfl

/--
Nonzero scalar multiplication on the divisor-compatible API.

Unlike addition, this operation is sound without germ quotients: multiplying by
a nonzero scalar preserves all zero, pole, and principal divisors.
-/
noncomputable def smulNonzero (c : ℂ) (hc : c ≠ 0)
    (f : MeromorphicFunctionWithDivisors X) : MeromorphicFunctionWithDivisors X :=
  { toFunction := c • f.toFunction
    germs := c • f.germs
    germs_eq_toFunction := by
      funext P
      ext
      rw [Pi.smul_apply, f.germs_eq_toFunction]
      simp [MeromorphicFunctionType.germFamily, MeromorphicFunctionType.germAt]
      apply Filter.EventuallyEq.germ_eq
      filter_upwards with Q
      change c * (f.toFunction.toFun Q).getD 0 =
        ((MeromorphicFunctionType.smul_meromorphic c f.toFunction).toFun Q).getD 0
      simp [MeromorphicFunctionType.smul_meromorphic, hc]
      cases f.toFunction.toFun Q <;> simp [Option.getD]
    zeroDivisor := f.zeroDivisor
    poleDivisor := f.poleDivisor
    principalDivisor := f.principalDivisor
    order := f.order
    zeroDivisor_apply := f.zeroDivisor_apply
    poleDivisor_apply := f.poleDivisor_apply
    principalDivisor_apply := f.principalDivisor_apply
    principalDivisor_eq := f.principalDivisor_eq
    poleDivisor_nonneg := f.poleDivisor_nonneg
    zero_or_pole_eq_zero := f.zero_or_pole_eq_zero
    toFun_ne_infty_of_poleDivisor_zero := by
      intro P hP
      have hfinite : f.toFunction.toFun P ≠ (OnePoint.infty : OnePoint ℂ) :=
        f.toFun_ne_infty_of_poleDivisor_zero P hP
      have hvalue :=
        MeromorphicFunctionType.smul_toFun c f.toFunction P hfinite
      rw [hvalue]
      exact OnePoint.coe_ne_infty _ }

@[simp] theorem smulNonzero_poles (c : ℂ) (hc : c ≠ 0)
    (f : MeromorphicFunctionWithDivisors X) :
    (smulNonzero c hc f).poles = f.poles :=
  rfl

@[simp] theorem smulNonzero_principal (c : ℂ) (hc : c ≠ 0)
    (f : MeromorphicFunctionWithDivisors X) :
    (smulNonzero c hc f).principal = f.principal :=
  rfl

theorem smulNonzero_memRiemannRochSpace_iff (c : ℂ) (hc : c ≠ 0)
    (f : MeromorphicFunctionWithDivisors X) (D : Divisor X) :
    (smulNonzero c hc f).MemRiemannRochSpace D ↔ f.MemRiemannRochSpace D := by
  rfl

/--
Explicit data for an addition result in the divisor-compatible API.

This is the replacement for the removed global `Add` instance.  A consumer may
use an `AddData f g` value once it has constructed the actual meromorphic sum
and proved the divisor-side facts, including whatever pole cancellation occurs
in that sum.
-/
structure AddData (f g : MeromorphicFunctionWithDivisors X) where
  result : MeromorphicFunctionWithDivisors X
  /--
The result's local germs are the genuine germ-wise sum.  This is the
  pole-cancelling additive datum missing from pointwise `OnePoint` addition.
-/
  germs_eq_add : result.germs = f.germs + g.germs
  /--
Local order lower bound for addition.  Strict inequality is where pole
  cancellation is recorded by the result's own order/divisor fields.
-/
  order_le_result : ∀ P : X, min (f.order P) (g.order P) ≤ result.order P
  /--
On points where both inputs are finite, the result has the expected
  finite value.  At poles this record intentionally makes no pointwise claim;
  cancellation is represented by the result's divisor fields.
-/
  toFun_eq_on_common_regular :
    ∀ P : X, f.poles P = 0 → g.poles P = 0 →
      result.toFunction.toFun P =
        (((f.toFunction.toFun P).getD 0 + (g.toFunction.toFun P).getD 0 : ℂ) :
          OnePoint ℂ)
  /--
Divisor-side membership preservation for a chosen Riemann-Roch bound.
  This is an explicit field rather than a global theorem because the proof
  depends on the actual cancellation behavior of the constructed sum.
-/
  memRiemannRochSpace_of_mem :
    ∀ D : Divisor X, f.MemRiemannRochSpace D → g.MemRiemannRochSpace D →
      result.MemRiemannRochSpace D

namespace AddData

variable {f g : MeromorphicFunctionWithDivisors X}

theorem result_memRiemannRochSpace (h : AddData f g) (D : Divisor X)
    (hf : f.MemRiemannRochSpace D) (hg : g.MemRiemannRochSpace D) :
    h.result.MemRiemannRochSpace D :=
  h.memRiemannRochSpace_of_mem D hf hg

@[simp] theorem germs_eq_add_at (h : AddData f g) (P : X) :
    h.result.germs P = f.germs P + g.germs P :=
  congr_fun h.germs_eq_add P

theorem order_bound (h : AddData f g) (P : X) :
    min (f.order P) (g.order P) ≤ h.result.order P :=
  h.order_le_result P

end AddData

end MeromorphicFunctionWithDivisors

end JacobianChallenge.HolomorphicForms
