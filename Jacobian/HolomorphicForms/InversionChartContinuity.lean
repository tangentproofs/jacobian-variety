import Jacobian.HolomorphicForms.OnePointCxIsManifold
import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.EntireZero
import Jacobian.HolomorphicForms.ChartSectionContDiff
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Topology.VectorBundle.Hom

/-!
# Continuity of cotangent section local representative in the inversion chart

Proves `ContMDiffSection_localRepr_inversionChart_continuousAt_zero`:
the function `w ↦ ω(inversionChart.symm w)(1)` is ContinuousAt at `w = 0`.

Every holomorphic 1-form on `OnePoint ℂ ≅ ℂℙ¹` is identically zero
(a consequence of Liouville's theorem). The ContinuousAt then follows
trivially because the function is identically zero.

The proof decomposes into:
1. **Identity chart coefficient is entire** (step G2a; the chart-trivialisation
   API it needs is proved in `ChartSectionContDiff.lean`)
2. **Identity chart coefficient tends to 0 at infinity** (from the
   inversion-chart trivialization analysis: the trivialized representative
   H(w) is smooth at 0, and `f(w⁻¹) = -w² H(w)(1)` gives `|f(z)| ≤ C/|z|²`)
3. **Liouville** → `f ≡ 0`
4. **Section vanishes at finite points** (from `f ≡ 0`)
5. **Section vanishes at ∞** (from trivialization + dense set argument)
6. **ContinuousAt** (trivial for the zero function)
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold Topology
open Filter

/-! ### Helpers -/

/-- A CLM `ℂ →L[ℂ] ℂ` that maps 1 to 0 is the zero map. -/
theorem clm_eq_zero_of_apply_one_eq_zero' (f : ℂ →L[ℂ] ℂ) (h : f 1 = 0) : f = 0 := by
  have : ∀ x : ℂ, f x = 0 := by
    intro x
    have := f.map_smul (x : ℂ) (1 : ℂ)
    simp at this
    rw [this, h, mul_zero]
  exact ContinuousLinearMap.ext this

/-!
### Step 1: Identity chart coefficient is entire

This is the content of step G2a. It needs the chart-trivialisation API for
`ContMDiffSection` on the cotangent bundle, which Mathlib does not provide;
that API is built project-locally in
`Jacobian/HolomorphicForms/ChartSectionContDiff.lean`
(`contMDiffSection_localRepr_identityChart_contDiff`), so nothing is assumed
here.
-/

/--
The identity chart coefficient `z ↦ ω(↑z)(1)` is `ContDiff`.
This is step G2a, proved by `contMDiffSection_localRepr_identityChart_contDiff`.
-/
theorem identityChartCoeff_contDiff (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContDiff ℂ ⊤ (fun z : ℂ => ω.toFun (↑z : OnePoint ℂ)
      (show TangentSpace (modelWithCornersSelf ℂ ℂ) (↑z : OnePoint ℂ) from (1 : ℂ))) := by
  convert contMDiffSection_localRepr_identityChart_contDiff ω using 1

/-- The identity chart coefficient is differentiable (entire). -/
theorem identityChartCoeff_differentiable (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    Differentiable ℂ (fun z : ℂ => ω.toFun (↑z : OnePoint ℂ)
      (show TangentSpace (modelWithCornersSelf ℂ ℂ) (↑z : OnePoint ℂ) from (1 : ℂ))) :=
  (identityChartCoeff_contDiff ω).differentiable (by simp)

/-!
### Step 2: Identity chart coefficient tends to 0 at infinity

The trivialized inversion-chart representative `H(w)` is smooth at `w = 0`
(from `contMDiffAt_section_iff` at `∞`). The Hom-bundle trivialization
formula gives `f(w⁻¹) = -w² · H(w)(1)` for `w ≠ 0`. Since `H(w)(1)` is
bounded near `0`, we get `|f(z)| ≤ C/|z|²` for large `|z|`.
-/

/-! ##### Helpers for the chart-overlap computation at infinity -/

/-- Unfolding: `inversionChart` viewed as `OnePoint ℂ → ℂ` is `invFwd`. -/
private lemma inversionChart_coe : (inversionChart : OnePoint ℂ → ℂ) = invFwd := rfl

/-- Unfolding: `(identityChart.symm : ℂ → OnePoint ℂ) z = (z : OnePoint ℂ)`. -/
private lemma identityChart_symm_apply' (z : ℂ) :
    (identityChart.symm : ℂ → OnePoint ℂ) z = (z : OnePoint ℂ) := by
  rw [identityChart]
  simp [Topology.IsOpenEmbedding.toOpenPartialHomeomorph]

/-- The composition `inversionChart ∘ identityChart.symm : ℂ → ℂ` equals `Inv.inv` pointwise. -/
private lemma inversionChart_comp_identityChart_symm (w : ℂ) :
    inversionChart ((identityChart.symm : ℂ → OnePoint ℂ) w) = w⁻¹ := by
  rw [identityChart_symm_apply', inversionChart_coe]
  simp [invFwd]

/-- `extChartAt I ∞ = inversionChart` as a function. -/
private lemma extChartAt_infty_apply (p : OnePoint ℂ) :
    extChartAt (modelWithCornersSelf ℂ ℂ) (OnePoint.infty : OnePoint ℂ) p =
      (inversionChart : OnePoint ℂ → ℂ) p := by
  show ((chartAt ℂ (OnePoint.infty : OnePoint ℂ)).extend (modelWithCornersSelf ℂ ℂ)) p =
    inversionChart p
  rfl

/-- `(extChartAt I ↑z).symm = identityChart.symm` as a function. -/
private lemma extChartAt_some_symm_apply (z : ℂ) (w : ℂ) :
    (extChartAt (modelWithCornersSelf ℂ ℂ) (OnePoint.some z : OnePoint ℂ)).symm w =
      (identityChart.symm : ℂ → OnePoint ℂ) w := by
  rfl

/-- `identityChart` applied to `↑z` returns `z`. -/
private lemma identityChart_apply_some' (z : ℂ) :
    (identityChart : OnePoint ℂ → ℂ) (OnePoint.some z : OnePoint ℂ) = z := by
  show (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑·) : ℂ → OnePoint ℂ)).symm
    (OnePoint.some z) = z
  exact OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_left_inv

/-- `extChartAt I ↑z ↑z = z`. -/
private lemma extChartAt_some_self (z : ℂ) :
    extChartAt (modelWithCornersSelf ℂ ℂ) (OnePoint.some z : OnePoint ℂ)
        (OnePoint.some z : OnePoint ℂ) = z := by
  show (modelWithCornersSelf ℂ ℂ)
    ((chartAt ℂ (OnePoint.some z : OnePoint ℂ)) (OnePoint.some z : OnePoint ℂ)) = z
  show (modelWithCornersSelf ℂ ℂ)
    ((identityChart : OnePoint ℂ → ℂ) (OnePoint.some z : OnePoint ℂ)) = z
  rw [modelWithCornersSelf_coe, id_def, identityChart_apply_some']

/-- `range (modelWithCornersSelf ℂ ℂ) = univ`. -/
private lemma range_modelWithCornersSelf_eq_univ :
    Set.range (modelWithCornersSelf ℂ ℂ : ℂ → ℂ) = Set.univ := by
  simp [modelWithCornersSelf_coe]

/-! ##### Key tangent-trivialization formula at infinity -/

/--
For `z ≠ 0`, the tangent-bundle trivialization at `∞` evaluated on the
fiber at `↑z` is multiplication by `-(z^2)⁻¹` (representing the derivative of
the chart transition `w ↦ w⁻¹`).
-/
private lemma tangent_continuousLinearMapAt_inversion_apply
    (z : ℂ) (hz : z ≠ 0) (v : ℂ) :
    (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ))
        (OnePoint.infty : OnePoint ℂ)).continuousLinearMapAt ℂ (OnePoint.some z) v =
      -(z ^ 2)⁻¹ * v := by
  have hmem : (OnePoint.some z : OnePoint ℂ) ∈
      (chartAt ℂ (OnePoint.infty : OnePoint ℂ)).source := by
    show (OnePoint.some z : OnePoint ℂ) ∈ inversionChart.source
    show (OnePoint.some z : OnePoint ℂ) ∈ ({((0 : ℂ) : OnePoint ℂ)}ᶜ : Set (OnePoint ℂ))
    intro h
    exact hz (OnePoint.coe_injective h)
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hmem,
    tangentBundleCore_coordChange_achart]
  -- The composition `extChartAt I ∞ ∘ (extChartAt I ↑z).symm` is `(·⁻¹) : ℂ → ℂ`.
  have hfunc :
      Set.EqOn
        ((extChartAt (modelWithCornersSelf ℂ ℂ) (OnePoint.infty : OnePoint ℂ)) ∘
          (extChartAt (modelWithCornersSelf ℂ ℂ) (OnePoint.some z : OnePoint ℂ)).symm)
        (fun w : ℂ => w⁻¹) Set.univ := by
    intro w _
    show ((extChartAt (modelWithCornersSelf ℂ ℂ) (OnePoint.infty : OnePoint ℂ)) ∘
        (extChartAt (modelWithCornersSelf ℂ ℂ) (OnePoint.some z : OnePoint ℂ)).symm) w =
        w⁻¹
    rw [Function.comp]
    rw [extChartAt_some_symm_apply, extChartAt_infty_apply,
      inversionChart_comp_identityChart_symm]
  rw [extChartAt_some_self z]
  have huniqueDiff : UniqueDiffWithinAt ℂ
      (Set.range (modelWithCornersSelf ℂ ℂ : ℂ → ℂ)) z := by
    rw [range_modelWithCornersSelf_eq_univ]
    exact uniqueDiffWithinAt_univ
  have hinv_fderiv : HasFDerivWithinAt (fun w : ℂ => w⁻¹)
      (ContinuousLinearMap.toSpanSingleton ℂ (-(z ^ 2)⁻¹) : ℂ →L[ℂ] ℂ)
      (Set.range (modelWithCornersSelf ℂ ℂ : ℂ → ℂ)) z :=
    (hasFDerivAt_inv hz).hasFDerivWithinAt
  have h_eq_fderiv : HasFDerivWithinAt
      ((extChartAt (modelWithCornersSelf ℂ ℂ) (OnePoint.infty : OnePoint ℂ)) ∘
        (extChartAt (modelWithCornersSelf ℂ ℂ) (OnePoint.some z : OnePoint ℂ)).symm)
      (ContinuousLinearMap.toSpanSingleton ℂ (-(z ^ 2)⁻¹) : ℂ →L[ℂ] ℂ)
      (Set.range (modelWithCornersSelf ℂ ℂ : ℂ → ℂ)) z :=
    HasFDerivWithinAt.congr hinv_fderiv (fun w _ => hfunc (Set.mem_univ w))
      (hfunc (Set.mem_univ z))
  rw [h_eq_fderiv.fderivWithin huniqueDiff]
  show (ContinuousLinearMap.toSpanSingleton ℂ (-(z ^ 2)⁻¹)) v = -(z ^ 2)⁻¹ * v
  simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]

/-! ##### Cotangent trivialization: `(triv ⟨b, ω b⟩).snd = ω b ∘L symmL` -/

/--
The trivialization at `∞` of the cotangent bundle, applied to the section
value at `b`, equals `ω b` post-composed with the tangent-bundle `symmL` at
that point.
-/
private lemma cotangent_triv_inversion_snd
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) (b : OnePoint ℂ) :
    ((trivializationAt (CotangentModelFiber ℂ) (CotangentSpace ℂ (OnePoint ℂ))
          (OnePoint.infty : OnePoint ℂ)) ⟨b, ω.toFun b⟩).snd =
      (ω.toFun b).comp
        ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ))
          (OnePoint.infty : OnePoint ℂ)).symmL ℂ b) := by
  rw [show (trivializationAt (CotangentModelFiber ℂ) (CotangentSpace ℂ (OnePoint ℂ))
        (OnePoint.infty : OnePoint ℂ)) =
      (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ))
        (OnePoint.infty : OnePoint ℂ)).continuousLinearMap (RingHom.id ℂ)
        (trivializationAt ℂ (Bundle.Trivial (OnePoint ℂ) ℂ)
          (OnePoint.infty : OnePoint ℂ)) from rfl,
    Bundle.Trivialization.continuousLinearMap_apply]
  have hTrivial :
      (trivializationAt ℂ (Bundle.Trivial (OnePoint ℂ) ℂ)
          (OnePoint.infty : OnePoint ℂ)).continuousLinearMapAt ℂ b =
        ContinuousLinearMap.id ℂ ℂ := by
    have h₀ : (Bundle.Trivial.trivialization (OnePoint ℂ) ℂ).continuousLinearMapAt ℂ b
        = ContinuousLinearMap.id ℂ ℂ :=
      Bundle.Trivial.continuousLinearMapAt_trivialization ℂ (OnePoint ℂ) ℂ b
    have hbridge :
        (trivializationAt ℂ (Bundle.Trivial (OnePoint ℂ) ℂ)
            (OnePoint.infty : OnePoint ℂ)).continuousLinearMapAt ℂ b =
          (Bundle.Trivial.trivialization (OnePoint ℂ) ℂ).continuousLinearMapAt ℂ b := by
      congr 1
    exact hbridge.trans h₀
  rw [hTrivial]
  rfl

/-! ##### Continuity of the trivialized section at `∞` -/

private lemma cotangent_triv_inversion_snd_continuousAt
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContinuousAt (fun b : OnePoint ℂ =>
      ((trivializationAt (CotangentModelFiber ℂ) (CotangentSpace ℂ (OnePoint ℂ))
          (OnePoint.infty : OnePoint ℂ)) ⟨b, ω.toFun b⟩).snd)
      (OnePoint.infty : OnePoint ℂ) := by
  set e := trivializationAt (CotangentModelFiber ℂ) (CotangentSpace ℂ (OnePoint ℂ))
    (OnePoint.infty : OnePoint ℂ)
  have hbase : (OnePoint.infty : OnePoint ℂ) ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (OnePoint.infty : OnePoint ℂ)
  have hopen : IsOpen e.baseSet := e.open_baseSet
  have hcont_lift :
      ContinuousOn (fun b : OnePoint ℂ =>
        e ⟨b, ω.toFun b⟩) e.baseSet := by
    refine e.continuousOn.comp ?_ ?_
    · exact Continuous.continuousOn ω.contMDiff_toFun.continuous
    · intro b hb; exact e.mem_source.mpr hb
  have hcont_snd :
      ContinuousOn (fun b : OnePoint ℂ =>
        (e ⟨b, ω.toFun b⟩).snd) e.baseSet :=
    ContinuousOn.snd hcont_lift
  exact hcont_snd.continuousAt (hopen.mem_nhds hbase)

/-! ##### Assembling the tendsto statement -/

theorem identityChartCoeff_tendsto_zero (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    Tendsto (fun z : ℂ => ω.toFun (↑z : OnePoint ℂ)
      (show TangentSpace (modelWithCornersSelf ℂ ℂ) (↑z : OnePoint ℂ) from (1 : ℂ)))
      (cocompact ℂ) (nhds 0) := by
  set f : ℂ → ℂ := fun z =>
    ω.toFun (↑z : OnePoint ℂ)
      (show TangentSpace (modelWithCornersSelf ℂ ℂ) (↑z : OnePoint ℂ) from (1 : ℂ))
    with hf_def
  -- `H b` is the trivialized cotangent section at `b` (a CLM `ℂ →L[ℂ] ℂ`).
  set H : OnePoint ℂ → (ℂ →L[ℂ] ℂ) := fun b =>
    ((trivializationAt (CotangentModelFiber ℂ) (CotangentSpace ℂ (OnePoint ℂ))
        (OnePoint.infty : OnePoint ℂ)) ⟨b, ω.toFun b⟩).snd
    with hH_def
  -- Step A: `b ↦ H b (1)` is continuous at `∞`.
  have hH_cont : ContinuousAt H (OnePoint.infty : OnePoint ℂ) :=
    cotangent_triv_inversion_snd_continuousAt ω
  have hH_apply_cont :
      ContinuousAt (fun b : OnePoint ℂ => H b (1 : ℂ)) (OnePoint.infty : OnePoint ℂ) :=
    ContinuousAt.clm_apply hH_cont continuousAt_const
  -- Step B: `w ↦ H (invBwd w) (1)` is continuous at `0`.
  have hinvBwd_cont : ContinuousAt invBwd 0 := by
    have hcont : ContinuousOn invBwd Set.univ := continuousOn_invBwd
    have : invBwd 0 = (OnePoint.infty : OnePoint ℂ) := invBwd_zero
    exact hcont.continuousAt (by simp)
  have hg_cont : ContinuousAt (fun w : ℂ => H (invBwd w) (1 : ℂ)) 0 := by
    have h₁ : invBwd 0 = (OnePoint.infty : OnePoint ℂ) := invBwd_zero
    have hatinfty : ContinuousAt (fun b : OnePoint ℂ => H b (1 : ℂ)) (invBwd 0) := by
      rw [h₁]; exact hH_apply_cont
    exact hatinfty.comp hinvBwd_cont
  -- Step C: bounded near 0.
  obtain ⟨M, hM⟩ : ∃ M, ∀ᶠ w in nhds (0 : ℂ), ‖H (invBwd w) (1 : ℂ)‖ ≤ M := by
    set g : ℂ → ℂ := fun w => H (invBwd w) (1 : ℂ)
    have hgn : Tendsto (fun w => ‖g w‖) (nhds (0 : ℂ)) (nhds ‖g 0‖) :=
      (continuous_norm.continuousAt).comp hg_cont
    refine ⟨‖g 0‖ + 1, ?_⟩
    have : ∀ᶠ w in nhds (0 : ℂ), ‖g w‖ < ‖g 0‖ + 1 :=
      hgn.eventually (eventually_lt_nhds (by linarith))
    filter_upwards [this] with w hw using hw.le
  -- Step D: For `w ≠ 0`, the trivialization formula gives
  --   `H (invBwd w) (1) = -w⁻² * f (w⁻¹)`, equivalently
  --   `f (w⁻¹) = -w² * H (invBwd w) (1)`.
  have hformula :
      ∀ w : ℂ, w ≠ 0 → f (w⁻¹) = -w ^ 2 * H (invBwd w) (1 : ℂ) := by
    intro w hw
    have hwinv : w⁻¹ ≠ 0 := inv_ne_zero hw
    -- Unfold `invBwd w = ↑(w⁻¹)`.
    have hinv : invBwd w = (OnePoint.some (w⁻¹) : OnePoint ℂ) := invBwd_ne_zero hw
    rw [hinv]
    -- Use cotangent trivialization formula.
    have hH_eq :
        H (OnePoint.some (w⁻¹) : OnePoint ℂ) =
          (ω.toFun (OnePoint.some (w⁻¹) : OnePoint ℂ)).comp
            ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ))
              (OnePoint.infty : OnePoint ℂ)).symmL ℂ
              (OnePoint.some (w⁻¹) : OnePoint ℂ)) :=
      cotangent_triv_inversion_snd ω (OnePoint.some (w⁻¹) : OnePoint ℂ)
    -- Apply both sides to 1.
    have hH_apply :
        H (OnePoint.some (w⁻¹) : OnePoint ℂ) (1 : ℂ) =
          (ω.toFun (OnePoint.some (w⁻¹) : OnePoint ℂ))
            ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ))
              (OnePoint.infty : OnePoint ℂ)).symmL ℂ
              (OnePoint.some (w⁻¹) : OnePoint ℂ) (1 : ℂ)) := by
      rw [hH_eq]; rfl
    -- Compute `symmL`-of-1 using `symmL_continuousLinearMapAt` and
    -- the explicit `continuousLinearMapAt` formula.
    have htan_mem :
        (OnePoint.some (w⁻¹) : OnePoint ℂ) ∈
          (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ))
            (OnePoint.infty : OnePoint ℂ)).baseSet := by
      show (OnePoint.some (w⁻¹) : OnePoint ℂ) ∈ inversionChart.source
      show (OnePoint.some (w⁻¹) : OnePoint ℂ) ∈ ({((0 : ℂ) : OnePoint ℂ)}ᶜ : Set (OnePoint ℂ))
      intro h
      exact hwinv (OnePoint.coe_injective h)
    -- The continuousLinearMapAt formula at `↑(w⁻¹)` gives
    --   `cLMA v = -((w⁻¹)^2)⁻¹ · v`.
    -- We pick `v := -((w⁻¹)^2)⁻¹ · (-1)^{-1}`... actually pick `v = something`
    -- so that `cLMA v = 1`. We need `-((w⁻¹)^2)⁻¹ · v = 1`,
    -- i.e. `v = -(w⁻¹)^2`.
    have hwwinv : w * w⁻¹ = (1 : ℂ) := mul_inv_cancel₀ hw
    have hcLMA_apply :
        (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ))
          (OnePoint.infty : OnePoint ℂ)).continuousLinearMapAt ℂ
          (OnePoint.some (w⁻¹) : OnePoint ℂ) (-(w⁻¹) ^ 2) = (1 : ℂ) := by
      have hfm := tangent_continuousLinearMapAt_inversion_apply (w⁻¹) hwinv
        (-(w⁻¹) ^ 2)
      -- `rw`/`simp` can't see the LHS (its argument lives in the fiber type
      -- `TangentSpace 𝓘(ℂ,ℂ) ↑w⁻¹`, defeq to ℂ but not syntactically); close
      -- in term mode where the fiber defeq is transparent.
      refine hfm.trans ?_
      -- Goal: -((w⁻¹)^2)⁻¹ * -(w⁻¹)^2 = 1
      have hsqne : ((w⁻¹) ^ 2 : ℂ) ≠ 0 := pow_ne_zero _ hwinv
      field_simp
    have hsymmL_one :
        (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ))
          (OnePoint.infty : OnePoint ℂ)).symmL ℂ
          (OnePoint.some (w⁻¹) : OnePoint ℂ) (1 : ℂ) = (-(w⁻¹) ^ 2 : ℂ) := by
      have hround :
          (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ))
            (OnePoint.infty : OnePoint ℂ)).symmL ℂ
              (OnePoint.some (w⁻¹) : OnePoint ℂ)
            ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ))
              (OnePoint.infty : OnePoint ℂ)).continuousLinearMapAt ℂ
                (OnePoint.some (w⁻¹) : OnePoint ℂ) (-(w⁻¹) ^ 2 : ℂ)) =
            (-(w⁻¹) ^ 2 : ℂ) :=
        Bundle.Trivialization.symmL_continuousLinearMapAt
          (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ))
            (OnePoint.infty : OnePoint ℂ)) htan_mem (-(w⁻¹) ^ 2)
      exact hcLMA_apply ▸ hround
    rw [hH_apply, hsymmL_one]
    -- `H(↑w⁻¹)(1) = ω(↑w⁻¹)(-(w⁻¹)^2) = -(w⁻¹)^2 · f(w⁻¹)`.
    -- Goal: `f(w⁻¹) = -w^2 * (-(w⁻¹)^2 · f(w⁻¹))`.
    -- `ω.toFun ↑w⁻¹` is ℂ-linear; its argument `-w⁻¹^2` lives in the fiber
    -- `TangentSpace 𝓘(ℂ,ℂ) ↑w⁻¹` (defeq ℂ, not syntactic), so `rw [map_smul]`
    -- can't match — establish the value equation in term mode instead.
    have hfw : (ω.toFun (OnePoint.some (w⁻¹) : OnePoint ℂ)) (1 : ℂ) = f w⁻¹ := rfl
    have hval : (ω.toFun (OnePoint.some (w⁻¹) : OnePoint ℂ)) (-(w⁻¹) ^ 2)
        = -(w⁻¹) ^ 2 * f w⁻¹ := by
      -- `ω(↑w⁻¹)` is ℂ-linear; `-w⁻¹^2 = (-w⁻¹^2) • (1 : fiber)` definitionally,
      -- so `map_smul` gives the value.  Use `map_smul` directly on `-w⁻¹^2` viewed
      -- as a scalar times the fiber unit, and discharge the fiber-`smul` defeqs by `simp`.
      have hlin :=
        (ω.toFun (OnePoint.some (w⁻¹) : OnePoint ℂ)).map_smul (-(w⁻¹) ^ 2 : ℂ) (1 : ℂ)
      simp only [smul_eq_mul, hfw] at hlin
      refine Eq.trans ?_ hlin
      congr 1
      show (-(w⁻¹) ^ 2 : ℂ) = (-(w⁻¹) ^ 2 : ℂ) • (1 : ℂ)
      rw [smul_eq_mul, mul_one]
    have hcancel : -w ^ 2 * (-(w⁻¹) ^ 2) = (1 : ℂ) := by
      rw [show -w ^ 2 * (-(w⁻¹) ^ 2) = (w * w⁻¹) ^ 2 by ring, hwwinv]
      ring
    calc f w⁻¹ = (-w ^ 2 * (-(w⁻¹) ^ 2)) * f w⁻¹ := by rw [hcancel, one_mul]
      _ = -w ^ 2 * (-(w⁻¹) ^ 2 * f w⁻¹) := by ring
      _ = -w ^ 2 * (ω.toFun (OnePoint.some (w⁻¹) : OnePoint ℂ)) (-(w⁻¹) ^ 2) := by rw [hval]
  -- Step E: limit `f (w⁻¹) → 0` as `w → 0`.
  have hsq_tendsto :
      Tendsto (fun w : ℂ => -w ^ 2 * H (invBwd w) (1 : ℂ)) (nhds (0 : ℂ)) (nhds 0) := by
    have hsq : Tendsto (fun w : ℂ => -w ^ 2) (nhds (0 : ℂ)) (nhds 0) := by
      have h := (continuous_neg.comp (continuous_pow 2)).tendsto (0 : ℂ)
      have hpow : ((0 : ℂ) ^ 2) = 0 := by norm_num
      simpa only [Function.comp_def, neg_zero, hpow] using h
    refine Filter.Tendsto.zero_mul_isBoundedUnder_le hsq ?_
    refine ⟨M, Filter.eventually_map.mpr ?_⟩
    filter_upwards [hM] with w hw using hw
  have hf_inv_tendsto :
      Tendsto (fun w : ℂ => f (w⁻¹)) (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds 0) := by
    refine (hsq_tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (hformula w hw).symm
  -- Step F: convert to `cocompact ℂ` via `tendsto_inv₀_cobounded'` and
  -- `Metric.cobounded_eq_cocompact`.
  have hinv : Tendsto (Inv.inv : ℂ → ℂ) (Bornology.cobounded ℂ) (nhdsWithin 0 {0}ᶜ) :=
    Filter.tendsto_inv₀_cobounded'
  have hf_comp_inv :
      Tendsto ((fun w : ℂ => f (w⁻¹)) ∘ Inv.inv) (Bornology.cobounded ℂ) (nhds 0) :=
    hf_inv_tendsto.comp hinv
  have h_eq_f : (fun w : ℂ => f (w⁻¹)) ∘ Inv.inv = f := by
    funext w; simp [Function.comp, inv_inv]
  rw [h_eq_f] at hf_comp_inv
  rw [Metric.cobounded_eq_cocompact] at hf_comp_inv
  exact hf_comp_inv

/-! ### Step 3: Liouville → f ≡ 0 -/

theorem identityChartCoeff_eq_zero (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) (z : ℂ) :
    ω.toFun (↑z : OnePoint ℂ)
      (show TangentSpace (modelWithCornersSelf ℂ ℂ) (↑z : OnePoint ℂ) from (1 : ℂ)) = 0 := by
  have hd := identityChartCoeff_differentiable ω
  have ht := identityChartCoeff_tendsto_zero ω
  have h := hd.eq_zero_of_tendsto_zero_cocompact ht
  exact congr_fun h z

/-! ### Step 4: Section vanishes at finite points -/

theorem section_finite_eq_zero' (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) (z : ℂ) :
    ω.toFun (↑z : OnePoint ℂ) = 0 :=
  clm_eq_zero_of_apply_one_eq_zero' _ (identityChartCoeff_eq_zero ω z)

/-! ### Step 5: Section vanishes at ∞ -/

/-
The section is zero at ∞. Uses the trivialization at ∞: the trivialized
representative `H(x)` is continuous, `H(↑z) = 0` for `z ≠ 0` (since
`ω(↑z) = 0`), and the dense subset argument gives `H(∞) = 0 = ω(∞)`.
-/
theorem section_infty_eq_zero' (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ω.toFun (OnePoint.infty : OnePoint ℂ) = 0 := by
  by_contra h_nonzero;
  -- Let $e$ be the trivialization at $\infty$.
  set e := trivializationAt (CotangentModelFiber ℂ) (CotangentSpace ℂ (OnePoint ℂ)) (OnePoint.infty);
  -- Let $H(x) = (e ⟨x, ω(x)⟩).2$ for $x ∈ e.baseSet$.
  set H : OnePoint ℂ → ℂ →L[ℂ] ℂ := fun x => (e ⟨x, ω x⟩).2;
  have hH_cont : ContinuousOn H e.baseSet := by
    have hH_cont : ContinuousOn (fun x => e ⟨x, ω x⟩) e.baseSet := by
      refine' e.continuousOn.comp _ _;
      · refine' Continuous.continuousOn _;
        have := ω.2;
        convert this.continuous using 1;
      · intro x hx; aesop;
    exact ContinuousOn.snd hH_cont
  have hH_zero : ∀ z : ℂ, z ≠ 0 → H (OnePoint.some z) = 0 := by
    -- Since $ω(z) = 0$ for all $z ≠ 0$, we have $H(z) = 0$ for all $z ≠ 0$.
    intros z hz
    have hω_zero : ω.toFun (OnePoint.some z) = 0 := by
      nontriviality;
      exact section_finite_eq_zero' ω z
    simp [H];
    convert e.zeroSection _ _;
    any_goals exact OnePoint.some z;
    any_goals exact ℂ;
    all_goals try infer_instance;
    · constructor <;> intro h <;> simp_all [ Prod.ext_iff ];
      · convert e.zeroSection _ _;
        any_goals exact OnePoint.some z;
        any_goals exact ℂ;
        all_goals try infer_instance;
        · simp [ Prod.ext_iff, Bundle.zeroSection ];
        · simp [ e ];
          simp [ chartAt ];
          simp [ ChartedSpace.chartAt ];
          simp [ inversionChart, hz ];
      · convert h.2;
    · simp +zetaDelta at *;
      simp [ chartAt ];
      simp [ ChartedSpace.chartAt ];
      simp [ inversionChart, hz ]
  have hH_zero_base : H OnePoint.infty = 0 := by
    have hH_zero_base : ∀ᶠ x in nhdsWithin OnePoint.infty {OnePoint.infty}ᶜ, H x = 0 := by
      rw [ eventually_nhdsWithin_iff ];
      rw [ OnePoint.nhds_infty_eq ];
      simp +zetaDelta at *;
      exact Filter.mem_of_superset ( Filter.mem_of_superset ( Filter.mem_cocompact.mpr ⟨ Metric.closedBall 0 1, ProperSpace.isCompact_closedBall _ _, by aesop_cat ⟩ ) fun x hx => by aesop_cat ) fun x hx => hH_zero x hx;
    convert tendsto_nhds_unique ( hH_cont.continuousAt ( IsOpen.mem_nhds ( show IsOpen e.baseSet from ?_ ) <| by aesop ) |> fun h => h.mono_left inf_le_left ) ( tendsto_nhds_of_eventually_eq hH_zero_base ) using 1;
    exact e.open_baseSet
  have hω_infty : ω.toFun OnePoint.infty = 0 := by
    have hω_infty : e ⟨OnePoint.infty, ω.toFun OnePoint.infty⟩ = e ⟨OnePoint.infty, 0⟩ := by
      have hω_infty : (e ⟨OnePoint.infty, ω.toFun OnePoint.infty⟩).2 = (e ⟨OnePoint.infty, 0⟩).2 := by
        convert hH_zero_base using 1;
        convert e.zeroSection _;
        any_goals exact ℂ;
        all_goals try infer_instance;
        exact ⟨ fun h => fun _ => Prod.ext rfl h, fun h => h ( by simp [ e ] ) |> congr_arg Prod.snd ⟩;
      exact Prod.ext ( by aesop ) hω_infty;
    have := e.injOn ( show { proj := OnePoint.infty, snd := ω.toFun OnePoint.infty } ∈ e.source from ?_ ) ( show { proj := OnePoint.infty, snd := 0 } ∈ e.source from ?_ ) hω_infty ; aesop;
    · simp [ e, Bundle.Trivialization.source_eq ];
    · simp [ e.mem_source ];
      exact FiberBundle.mem_baseSet_trivializationAt' OnePoint.infty
  exact h_nonzero hω_infty;

/-! ### Assembly -/

theorem holomorphicOneForm_onePointCx_eq_zero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) (x : OnePoint ℂ) :
    ω.toFun x = 0 := by
  cases x using OnePoint.rec with
  | infty => exact section_infty_eq_zero' ω
  | coe z => exact section_finite_eq_zero' ω z

theorem ContMDiffSection_localRepr_inversionChart_continuousAt_zero_proof
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContinuousAt (fun w => ω.toFun (inversionChart.symm w)
      (show TangentSpace (modelWithCornersSelf ℂ ℂ)
        (inversionChart.symm w) from (1 : ℂ))) 0 := by
  have h : ∀ w, ω.toFun (inversionChart.symm w)
      (show TangentSpace (modelWithCornersSelf ℂ ℂ)
        (inversionChart.symm w) from (1 : ℂ)) = 0 := by
    intro w
    rw [holomorphicOneForm_onePointCx_eq_zero ω]
    exact ContinuousLinearMap.zero_apply _
  simp only [h]
  exact continuousAt_const

end JacobianChallenge.HolomorphicForms
