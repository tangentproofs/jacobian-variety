import Jacobian.Surface.Smooth

/-!
# Forms on a Riemann surface as chart families; Stokes

A family `θ : X → ℂ → ℂ` gives a reading `θ p` in the chart at every point `p`.

* `Is01 θ`: `θ_p = conj(τ') θ_q ∘ τ` (a `(0,1)`-form, `θ_p dz̄`);
* `Is10 β`: `β_p = τ' β_q ∘ τ` (a `(1,0)`-form, `β_p dz`); holomorphic 1-forms (`holoF`);
* densities (`IsDensity`) from products: `(1,0)·(0,1)`, `conj(0,1)·(0,1)`, ….
* `dbarF u`, `dzF u`: `∂̄u`, `∂u`; `dzFam γ`, `dbarFam β`: `∂` of a `(0,1)`-form and `∂̄` of a
  `(1,0)`-form, which are densities.
* **Stokes** (`integral_dzFam_eq_zero`, `integral_dbarFam_eq_zero`): on a compact surface the
  integral of `∂γ` (resp. `∂̄β`) vanishes. Proof: split with the partition of unity, localize
  each piece to one chart (`integral_density_eq_chart`), and integrate by parts in the plane.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff

/-! ### More Wirtinger calculus -/

theorem dz_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dz (fun w => f w * g w) z = f z * dz g z + g z * dz f z := by
  unfold dz
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem dz_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : dz (fun w => f w + g w) z = dz f z + dz g z := by
  unfold dz
  rw [fderiv_fun_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

theorem dz_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {z : ℂ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    dz (fun w => ∑ i ∈ s, f i w) z = ∑ i ∈ s, dz (f i) z := by
  unfold dz
  rw [fderiv_fun_sum hf]
  simp only [ContinuousLinearMap.sum_apply, ← Finset.sum_div, Finset.mul_sum,
    ← Finset.sum_sub_distrib]

theorem dbar_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {z : ℂ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    dbar (fun w => ∑ i ∈ s, f i w) z = ∑ i ∈ s, dbar (f i) z := by
  unfold dbar
  rw [fderiv_fun_sum hf]
  simp only [ContinuousLinearMap.sum_apply, ← Finset.sum_div, Finset.mul_sum,
    ← Finset.sum_add_distrib]

theorem fderiv_conj_apply {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g z) (v : ℂ) :
    fderiv ℝ (fun w => (starRingEnd ℂ) (g w)) z v = (starRingEnd ℂ) (fderiv ℝ g z v) := by
  have h := (Complex.conjCLE.hasFDerivAt.comp z hg.hasFDerivAt).fderiv
  rw [show (fun w => (starRingEnd ℂ) (g w)) = Complex.conjCLE ∘ g from rfl, h]
  rfl

theorem dz_conj {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g z) :
    dz (fun w => (starRingEnd ℂ) (g w)) z = (starRingEnd ℂ) (dbar g z) := by
  unfold dz dbar
  rw [fderiv_conj_apply hg, fderiv_conj_apply hg]
  simp only [map_div₀, map_add, map_mul, Complex.conj_I, map_ofNat]
  ring

theorem dbar_conj {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => (starRingEnd ℂ) (g w)) z = (starRingEnd ℂ) (dz g z) := by
  unfold dz dbar
  rw [fderiv_conj_apply hg, fderiv_conj_apply hg]
  simp only [map_div₀, map_sub, map_mul, Complex.conj_I, map_ofNat]
  ring

theorem dz_eq_zero_of_eventuallyEq {f : ℂ → ℂ} {z c : ℂ} (h : f =ᶠ[𝓝 z] fun _ => c) :
    dz f z = 0 := by
  unfold dz; rw [h.fderiv_eq]; simp

theorem dz_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : dz f z = dz g z := by
  unfold dz; rw [h.fderiv_eq]

theorem dbar_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : dbar f z = dbar g z := by
  unfold dbar; rw [h.fderiv_eq]

theorem contDiffOn_dbar {f : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (dbar f) s := by
  have h := hf.fderiv_of_isOpen hs (m := ∞) (by simp)
  unfold dbar
  exact ((h.clm_apply contDiffOn_const).add
    (contDiffOn_const.mul (h.clm_apply contDiffOn_const))).div_const _

theorem contDiffOn_dz {f : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (dz f) s := by
  have h := hf.fderiv_of_isOpen hs (m := ∞) (by simp)
  unfold dz
  exact ((h.clm_apply contDiffOn_const).sub
    (contDiffOn_const.mul (h.clm_apply contDiffOn_const))).div_const _

/-- `∫ ∂φ/∂z̄ = 0` for compactly supported `C¹` functions. -/
theorem integral_dbar_eq_zero {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) :
    ∫ z, dbar φ z = 0 := by
  have := integral_mul_dbar (g := fun _ => (1 : ℂ)) contDiff_const hφ hs
  simp only [one_mul] at this
  rw [this]
  have h0 : dbar (fun _ : ℂ => (1 : ℂ)) = fun _ => 0 := by
    funext z; exact dbar_eq_zero_of_eventuallyEq (c := 1) (Eventually.of_forall fun _ => rfl)
  simp [h0]

theorem differentiableAt_conj_comp {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g z) :
    DifferentiableAt ℝ (fun w => (starRingEnd ℂ) (g w)) z :=
  Complex.conjCLE.differentiableAt.comp z hg

/-- `∫ ∂φ/∂z = 0` for compactly supported `C¹` functions. -/
theorem integral_dz_eq_zero {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) :
    ∫ z, dz φ z = 0 := by
  have hc : ContDiff ℝ 1 fun w => (starRingEnd ℂ) (φ w) :=
    Complex.conjCLE.contDiff.comp hφ
  have hcs : HasCompactSupport fun w => (starRingEnd ℂ) (φ w) := hs.comp_left (map_zero _)
  have e : ∀ z, dz φ z = (starRingEnd ℂ) (dbar (fun w => (starRingEnd ℂ) (φ w)) z) := by
    intro z
    rw [← dz_conj ((hc.differentiable one_ne_zero) z)]
    simp
  simp_rw [e]
  rw [integral_conj, integral_dbar_eq_zero hc hcs, map_zero]

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-! ### Families -/

/-- A `(0,1)`-form, given by its readings in all charts. -/
def Is01 (θ : X → ℂ → ℂ) : Prop :=
  ∀ p q : X, ∀ w ∈ overlap p q,
    θ p w = (starRingEnd ℂ) (deriv (trans p q) w) * θ q (trans p q w)

/-- A `(1,0)`-form, given by its readings in all charts. -/
def Is10 (β : X → ℂ → ℂ) : Prop :=
  ∀ p q : X, ∀ w ∈ overlap p q, β p w = deriv (trans p q) w * β q (trans p q w)

/-- All readings are smooth on their chart targets. -/
def SmoothFam (θ : X → ℂ → ℂ) : Prop := ∀ p : X, ContDiffOn ℝ ∞ (θ p) (chartAt ℂ p).target

theorem SmoothFam.differentiableAt {θ : X → ℂ → ℂ} (h : SmoothFam θ) {p : X} {w : ℂ}
    (hw : w ∈ (chartAt ℂ p).target) : DifferentiableAt ℝ (θ p) w :=
  ((h p).contDiffAt ((chartAt ℂ p).open_target.mem_nhds hw)).differentiableAt (by simp)

theorem IsSmooth.differentiableAt {u : X → ℂ} (h : IsSmooth u) {p : X} {w : ℂ}
    (hw : w ∈ (chartAt ℂ p).target) : DifferentiableAt ℝ (rd u p) w :=
  (h.contDiffAt hw).differentiableAt (by simp)

/-- `∂̄u`. -/
noncomputable def dbarF (u : X → ℂ) : X → ℂ → ℂ := fun p => dbar (rd u p)

/-- `∂u`. -/
noncomputable def dzF (u : X → ℂ) : X → ℂ → ℂ := fun p => dz (rd u p)

theorem dbarF_is01 {u : X → ℂ} (hu : IsSmooth u) : Is01 (dbarF u) := by
  intro p q w hw
  simp only [dbarF]
  rw [dbar_congr (rd_eventuallyEq hw)]
  exact dbar_comp_holo (hu.differentiableAt (trans_mem_overlap hw).1)
    (trans_differentiableAt hw)

theorem dzF_is10 {u : X → ℂ} (hu : IsSmooth u) : Is10 (dzF u) := by
  intro p q w hw
  simp only [dzF]
  rw [dz_congr (rd_eventuallyEq hw)]
  exact dz_comp_holo (hu.differentiableAt (trans_mem_overlap hw).1) (trans_differentiableAt hw)

theorem smoothFam_dbarF {u : X → ℂ} (hu : IsSmooth u) : SmoothFam (dbarF u) := fun p =>
  contDiffOn_dbar (chartAt ℂ p).open_target (hu p)

theorem smoothFam_dzF {u : X → ℂ} (hu : IsSmooth u) : SmoothFam (dzF u) := fun p =>
  contDiffOn_dz (chartAt ℂ p).open_target (hu p)

/-- The readings of a holomorphic 1-form. -/
noncomputable def holoF (η : HolomorphicOneForm ℂ X) : X → ℂ → ℂ := fun p => chartCoeff p η

theorem holoF_is10 (η : HolomorphicOneForm ℂ X) : Is10 (holoF η) := fun _ _ _ hw =>
  chartCoeff_transition η hw.1 hw.2

theorem smoothFam_holoF (η : HolomorphicOneForm ℂ X) : SmoothFam (holoF η) := fun p =>
  (chartCoeff_differentiableOn p η).contDiffOn_real (chartAt ℂ p).open_target

/-- Pointwise conjugate. -/
noncomputable def conjF (θ : X → ℂ → ℂ) : X → ℂ → ℂ := fun p w => (starRingEnd ℂ) (θ p w)

theorem Is10.conjF {β : X → ℂ → ℂ} (h : Is10 β) : Is01 (conjF β) := fun p q w hw => by
  simp only [Surface.conjF, h p q w hw, map_mul]

theorem Is01.conjF {θ : X → ℂ → ℂ} (h : Is01 θ) : Is10 (conjF θ) := fun p q w hw => by
  simp only [Surface.conjF, h p q w hw, map_mul, Complex.conj_conj]

theorem SmoothFam.conjF {θ : X → ℂ → ℂ} (h : SmoothFam θ) : SmoothFam (conjF θ) := fun p =>
  (Complex.conjCLE.contDiff.comp_contDiffOn (h p) : _)

/-- `u · θ`. -/
noncomputable def smulF (u : X → ℂ) (θ : X → ℂ → ℂ) : X → ℂ → ℂ := fun p w => rd u p w * θ p w

theorem Is01.smulF {θ : X → ℂ → ℂ} (h : Is01 θ) (u : X → ℂ) : Is01 (smulF u θ) :=
  fun p q w hw => by simp only [Surface.smulF, h p q w hw, ← rd_trans (u := u) hw]; ring

theorem Is10.smulF {θ : X → ℂ → ℂ} (h : Is10 θ) (u : X → ℂ) : Is10 (smulF u θ) :=
  fun p q w hw => by simp only [Surface.smulF, h p q w hw, ← rd_trans (u := u) hw]; ring

theorem SmoothFam.smulF {θ : X → ℂ → ℂ} (h : SmoothFam θ) {u : X → ℂ} (hu : IsSmooth u) :
    SmoothFam (smulF u θ) := fun p => (hu p).mul (h p)

theorem Is01.add {a b : X → ℂ → ℂ} (ha : Is01 a) (hb : Is01 b) : Is01 (a + b) :=
  fun p q w hw => by simp only [Pi.add_apply, ha p q w hw, hb p q w hw]; ring

theorem Is01.sub {a b : X → ℂ → ℂ} (ha : Is01 a) (hb : Is01 b) : Is01 (a - b) :=
  fun p q w hw => by simp only [Pi.sub_apply, ha p q w hw, hb p q w hw]; ring

theorem Is01.smul {a : X → ℂ → ℂ} (ha : Is01 a) (c : ℂ) : Is01 (c • a) :=
  fun p q w hw => by simp only [Pi.smul_apply, smul_eq_mul, ha p q w hw]; ring

theorem Is10.add {a b : X → ℂ → ℂ} (ha : Is10 a) (hb : Is10 b) : Is10 (a + b) :=
  fun p q w hw => by simp only [Pi.add_apply, ha p q w hw, hb p q w hw]; ring

theorem Is10.sub {a b : X → ℂ → ℂ} (ha : Is10 a) (hb : Is10 b) : Is10 (a - b) :=
  fun p q w hw => by simp only [Pi.sub_apply, ha p q w hw, hb p q w hw]; ring

theorem Is10.smul {a : X → ℂ → ℂ} (ha : Is10 a) (c : ℂ) : Is10 (c • a) :=
  fun p q w hw => by simp only [Pi.smul_apply, smul_eq_mul, ha p q w hw]; ring

theorem SmoothFam.add {a b : X → ℂ → ℂ} (ha : SmoothFam a) (hb : SmoothFam b) :
    SmoothFam (a + b) := fun p => (ha p).add (hb p)

theorem SmoothFam.sub {a b : X → ℂ → ℂ} (ha : SmoothFam a) (hb : SmoothFam b) :
    SmoothFam (a - b) := fun p => (ha p).sub (hb p)

theorem SmoothFam.smul {a : X → ℂ → ℂ} (ha : SmoothFam a) (c : ℂ) :
    SmoothFam (c • a) := fun p => (contDiffOn_const (c := c)).mul (ha p)

/-! ### Densities from products -/

theorem conj_mul_self' (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.conj_mul']; push_cast; ring

/-- `θ · β` for `θ` of type `(0,1)` and `β` of type `(1,0)` is a density. -/
theorem isDensity_mul {θ β : X → ℂ → ℂ} (hθ : Is01 θ) (hβ : Is10 β) :
    DiscAtlas.IsDensity (fun p w => θ p w * β p w) := fun p q w hw => by
  dsimp only
  rw [hθ p q w hw, hβ p q w hw, ← conj_mul_self']; ring

/-- `conj(a) · b` for two `(0,1)`-forms is a density. -/
theorem isDensity_conj_mul_01 {a b : X → ℂ → ℂ} (ha : Is01 a) (hb : Is01 b) :
    DiscAtlas.IsDensity (fun p w => (starRingEnd ℂ) (a p w) * b p w) := fun p q w hw => by
  dsimp only
  rw [ha p q w hw, hb p q w hw, map_mul, Complex.conj_conj, ← conj_mul_self']; ring

/-- `conj(a) · b` for two `(1,0)`-forms is a density. -/
theorem isDensity_conj_mul_10 {a b : X → ℂ → ℂ} (ha : Is10 a) (hb : Is10 b) :
    DiscAtlas.IsDensity (fun p w => (starRingEnd ℂ) (a p w) * b p w) := fun p q w hw => by
  dsimp only
  rw [ha p q w hw, hb p q w hw, map_mul, ← conj_mul_self']; ring

theorem DiscAtlas.IsDensity.add {σ τ : X → ℂ → ℂ} (hσ : DiscAtlas.IsDensity σ)
    (hτ : DiscAtlas.IsDensity τ) : DiscAtlas.IsDensity (σ + τ) := fun p q w hw => by
  simp only [Pi.add_apply, hσ p q w hw, hτ p q w hw]; ring

theorem DiscAtlas.IsDensity.sub {σ τ : X → ℂ → ℂ} (hσ : DiscAtlas.IsDensity σ)
    (hτ : DiscAtlas.IsDensity τ) : DiscAtlas.IsDensity (σ - τ) := fun p q w hw => by
  simp only [Pi.sub_apply, hσ p q w hw, hτ p q w hw]; ring

/-! ### `∂` of a `(0,1)`-form and `∂̄` of a `(1,0)`-form -/

/-- `∂γ` for a `(0,1)`-form `γ` (a density). -/
noncomputable def dzFam (γ : X → ℂ → ℂ) : X → ℂ → ℂ := fun p => dz (γ p)

/-- `∂̄β` for a `(1,0)`-form `β` (a density). -/
noncomputable def dbarFam (β : X → ℂ → ℂ) : X → ℂ → ℂ := fun p => dbar (β p)

/-- The derivative of a transition map is holomorphic near points of the overlap. -/
theorem deriv_trans_differentiableAt {p q : X} {w : ℂ} (hw : w ∈ overlap p q) :
    DifferentiableAt ℂ (deriv (trans p q)) w :=
  ((chartMap_analyticAt contMDiff_id hw.1 hw.2).deriv).differentiableAt

theorem isDensity_dzFam {γ : X → ℂ → ℂ} (hγ : Is01 γ) (hs : SmoothFam γ) :
    DiscAtlas.IsDensity (dzFam γ) := by
  intro p q w hw
  simp only [dzFam]
  have hev : γ p =ᶠ[𝓝 w] fun v => (starRingEnd ℂ) (deriv (trans p q) v) *
      (γ q ∘ trans p q) v := by
    filter_upwards [(isOpen_overlap p q).mem_nhds hw] with v hv using hγ p q v hv
  rw [dz_congr hev]
  have hd := deriv_trans_differentiableAt hw
  have hg : DifferentiableAt ℝ (γ q ∘ trans p q) w :=
    (hs.differentiableAt (trans_mem_overlap hw).1).comp w
      ((trans_differentiableAt hw).restrictScalars ℝ)
  have hdr : DifferentiableAt ℝ (deriv (trans p q)) w := DifferentiableAt.restrictScalars ℝ hd
  rw [dz_mul (differentiableAt_conj_comp hdr) hg, dz_conj hdr,
    dbar_eq_zero_of_differentiableAt hd, map_zero, mul_zero, add_zero,
    dz_comp_holo (hs.differentiableAt (trans_mem_overlap hw).1) (trans_differentiableAt hw),
    ← mul_assoc, conj_mul_self']

theorem isDensity_dbarFam {β : X → ℂ → ℂ} (hβ : Is10 β) (hs : SmoothFam β) :
    DiscAtlas.IsDensity (dbarFam β) := by
  intro p q w hw
  simp only [dbarFam]
  have hev : β p =ᶠ[𝓝 w] fun v => deriv (trans p q) v * (β q ∘ trans p q) v := by
    filter_upwards [(isOpen_overlap p q).mem_nhds hw] with v hv using hβ p q v hv
  rw [dbar_congr hev]
  have hd := deriv_trans_differentiableAt hw
  have hg : DifferentiableAt ℝ (β q ∘ trans p q) w :=
    (hs.differentiableAt (trans_mem_overlap hw).1).comp w
      ((trans_differentiableAt hw).restrictScalars ℝ)
  rw [dbar_mul (DifferentiableAt.restrictScalars ℝ hd) hg, dbar_eq_zero_of_differentiableAt hd,
    mul_zero, add_zero, dbar_comp_holo (hs.differentiableAt (trans_mem_overlap hw).1)
      (trans_differentiableAt hw), ← mul_assoc, mul_comm (deriv _ w), conj_mul_self']

end JacobianChallenge.Surface
