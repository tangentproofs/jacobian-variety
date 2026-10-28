import Jacobian.Surface.FormalChain
import Jacobian.Periods.GenuinePeriodLattice
import Jacobian.Periods.PrimitiveCovering
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Jacobian.HolomorphicForms.AnalyticGenus

/-!
# Abel's theorem for two points

If a formal chain `C` has boundary `Q₂ - Q₁` (`Q₁ ≠ Q₂`) and `∫_C ω = 0` for every holomorphic
1-form `ω`, then `X` is homeomorphic to the Riemann sphere (`homeomorph_of_null_chain`).

Proof: the `(0,1)`-form `θ C` pairs to `π ∫_C ω = 0` with every `ω`, so `θ C = ∂̄u`; the function
`F C · e^{-u}` is holomorphic off the vertices of `C`, and at a vertex `v` it is
`(w - w₀)^{ord C v}` times a smooth non-vanishing factor which is then holomorphic too
(`∂̄` vanishes on a punctured neighbourhood, hence at the centre by continuity). So it is a
meromorphic function with a single simple pole at `Q₁`, and `SimplePole.homeomorph` applies.

`two_point_separation`: in positive genus, Abel–Jacobi integrals from `P` to `Q₁` and to `Q₂`
differing by a period forces `Q₁ = Q₂`.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff

/-- A function smooth near `z₀` with `∂̄ = 0` on a punctured neighbourhood is holomorphic
at `z₀`. -/
theorem analyticAt_of_dbar_punctured {G : ℂ → ℂ} {z₀ : ℂ}
    (hG : ∀ᶠ w in 𝓝 z₀, ContDiffAt ℝ ∞ G w) (h0 : ∀ᶠ w in 𝓝[≠] z₀, dbar G w = 0) :
    AnalyticAt ℂ G z₀ := by
  have hc : ContinuousAt (dbar G) z₀ := by
    have hf := (hG.self_of_nhds.fderiv_right (m := 0) (by simp)).continuousAt
    unfold dbar
    exact ((hf.clm_apply continuousAt_const).add
      (continuousAt_const.mul (hf.clm_apply continuousAt_const))).div_const 2
  have hz : dbar G z₀ = 0 :=
    tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (h0.mono fun _ h => h.symm))
  have hall : ∀ᶠ w in 𝓝 z₀, dbar G w = 0 := by
    filter_upwards [eventually_nhdsWithin_iff.mp h0] with w hw
    by_cases hwz : w = z₀
    · rw [hwz]; exact hz
    · exact hw hwz
  have hd : ∀ᶠ w in 𝓝 z₀, DifferentiableAt ℂ G w := by
    filter_upwards [hG, hall] with w h1 h2 using
      differentiableAt_of_dbar_eq_zero (h1.differentiableAt (by simp)) h2
  exact DifferentiableOn.analyticAt (s := {w | DifferentiableAt ℂ G w})
    (fun w hw => (hw : DifferentiableAt ℂ G w).differentiableWithinAt) hd

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

namespace FChain

theorem ord_eq_zero_of_notMem (C : FChain X) {x : X} (hx : x ∉ V C) : ord C x = 0 := by
  induction C with
  | nil => rfl
  | cons c C ih =>
    rw [V_cons] at hx
    simp only [mem_union, mem_insert_iff, mem_singleton_iff, not_or] at hx
    rw [ord_cons, ih hx.2, Seg.ord, if_neg hx.1.2, if_neg hx.1.1]
    simp

/-- Near `x`, the punctured chart neighbourhood avoids the vertices. -/
theorem eventually_notMem_V (C : FChain X) (x : X) :
    ∀ᶠ w in 𝓝[≠] (chartAt ℂ x x),
      w ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm w ∉ V C := by
  have hcl : IsClosed (V C \ {x}) := ((V_finite C).diff).isClosed
  have hx : x ∉ V C \ {x} := fun h => h.2 rfl
  have hT := (chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x)
  have hs : ∀ᶠ w in 𝓝 (chartAt ℂ x x), (chartAt ℂ x).symm w ∉ V C \ {x} := by
    have := ((chartAt ℂ x).continuousAt_symm (mem_chart_target ℂ x)).preimage_mem_nhds
      (hcl.isOpen_compl.mem_nhds (by rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact hx))
    exact this
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hT, hs] with w hw1 hw2 hne
  refine ⟨hw1, fun hV => hw2 ⟨hV, fun hwx => hne ?_⟩⟩
  have := (chartAt ℂ x).right_inv hw1
  rw [show (chartAt ℂ x).symm w = x from hwx] at this
  exact this.symm

/-- `F C · e^{-u}`. -/
noncomputable def G (C : FChain X) (u : X → ℂ) (x : X) : ℂ := F C x * Complex.exp (-u x)

theorem rd_G (C : FChain X) (u : X → ℂ) (q : X) :
    rd (G C u) q = fun v => rd (F C) q v * Complex.exp (-rd u q v) := rfl

/-- Off the vertices, `F C · e^{-u}` is smooth with `∂̄ = 0` when `∂̄u = θ C`. -/
theorem G_local (C : FChain X) {u : X → ℂ} (hu : IsSmooth u)
    (hθu : ∀ q : X, ∀ w ∈ (chartAt ℂ q).target, θ C q w = dbar (rd u q) w)
    {q : X} {w : ℂ} (hw : w ∈ (chartAt ℂ q).target) (hV : (chartAt ℂ q).symm w ∉ V C) :
    ContDiffAt ℝ ∞ (rd (G C u) q) w ∧ dbar (rd (G C u) q) w = 0 := by
  obtain ⟨h1, h2⟩ := F_local C hw hV
  have hu' := hu.contDiffAt hw
  have he : ContDiffAt ℝ ∞ (fun v => Complex.exp (-rd u q v)) w :=
    ((Complex.contDiff_exp (𝕜 := ℂ) (n := ∞)).restrict_scalars ℝ).contDiffAt.comp w hu'.neg
  rw [rd_G]
  refine ⟨h1.mul he, ?_⟩
  have hneg : dbar (fun v => -rd u q v) w = -dbar (rd u q) w := by
    have := dbar_const_mul (-1) (hu'.differentiableAt (by simp)) (z := w)
    simpa using this
  rw [dbar_mul (h1.differentiableAt (by simp)) (he.differentiableAt (by simp)),
    dbar_cexp (hu'.neg.differentiableAt (by simp)), hneg, h2, ← hθu q w hw]
  ring

open Classical in
/-- The meromorphic function: `F C · e^{-u}`, corrected at the vertices. -/
noncomputable def mero (C : FChain X) (u : X → ℂ) (x : X) : ℂ :=
  if x ∈ V C then
    (if ord C x = 0 then (F_vertex C x).choose (chartAt ℂ x x) * Complex.exp (-u x) else 0)
  else G C u x

theorem rd_mero_eq_rd_G (C : FChain X) (u : X → ℂ) (x : X) :
    ∀ᶠ w in 𝓝[≠] (chartAt ℂ x x), rd (mero C u) x w = rd (G C u) x w := by
  filter_upwards [eventually_notMem_V C x] with w hw
  simp only [rd_apply, mero, if_neg hw.2]

/-- At any point, `mero = (w - w₀)^{ord} · H` near `w₀` (punctured), with `H` holomorphic and
non-vanishing at `w₀`. -/
theorem mero_local (C : FChain X) {u : X → ℂ} (hu : IsSmooth u)
    (hθu : ∀ q : X, ∀ w ∈ (chartAt ℂ q).target, θ C q w = dbar (rd u q) w) (x : X) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H (chartAt ℂ x x) ∧ H (chartAt ℂ x x) ≠ 0 ∧
      H (chartAt ℂ x x) = (F_vertex C x).choose (chartAt ℂ x x) * Complex.exp (-u x) ∧
      ∀ᶠ w in 𝓝[≠] (chartAt ℂ x x),
        rd (mero C u) x w = (w - chartAt ℂ x x) ^ (ord C x) * H w := by
  set w₀ := chartAt ℂ x x
  obtain ⟨hK, hK0, hev⟩ := (F_vertex C x).choose_spec
  set K := (F_vertex C x).choose
  set H : ℂ → ℂ := fun w => K w * Complex.exp (-rd u x w)
  have hT := (chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x)
  have hHs : ∀ᶠ w in 𝓝 w₀, ContDiffAt ℝ ∞ H w := by
    filter_upwards [hK, hT] with w h1 h2
    exact h1.mul (((Complex.contDiff_exp (𝕜 := ℂ) (n := ∞)).restrict_scalars ℝ).contDiffAt.comp
      w (hu.contDiffAt h2).neg)
  have hrel : ∀ᶠ w in 𝓝[≠] w₀, rd (mero C u) x w = (w - w₀) ^ (ord C x) * H w := by
    filter_upwards [rd_mero_eq_rd_G C u x, hev] with w h1 h2
    rw [h1, rd_G]
    simp only [H]
    rw [h2]; ring
  -- `H` is holomorphic: `∂̄H = 0` on the punctured neighbourhood
  have hH0 : ∀ᶠ w in 𝓝[≠] w₀, dbar H w = 0 := by
    have hopen : ∀ᶠ w in 𝓝[≠] w₀, ∀ᶠ v in 𝓝 w, v ≠ w₀ ∧ v ∈ (chartAt ℂ x).target ∧
        (chartAt ℂ x).symm v ∉ V C ∧ (rd (F C) x v = (v - w₀) ^ (ord C x) * K v) := by
      have h := (eventually_notMem_V C x).and hev
      rw [eventually_nhdsWithin_iff] at h
      have h' := h.eventually_nhds
      rw [eventually_nhdsWithin_iff]
      filter_upwards [h'] with w hw hne
      filter_upwards [hw, isOpen_ne.mem_nhds hne] with v hv hvne
      exact ⟨hvne, (hv hvne).1.1, (hv hvne).1.2, (hv hvne).2⟩
    filter_upwards [hopen, self_mem_nhdsWithin] with w hw hne
    obtain ⟨hgl, hdg⟩ := G_local C hu hθu hw.self_of_nhds.2.1 hw.self_of_nhds.2.2.1
    have hpow : AnalyticAt ℂ (fun v => (v - w₀) ^ (-ord C x)) w :=
      ((analyticAt_id.sub analyticAt_const).zpow (by
        simp only [Pi.sub_apply, id]; exact sub_ne_zero.mpr hne))
    have heq : H =ᶠ[𝓝 w] fun v => (v - w₀) ^ (-ord C x) * rd (G C u) x v := by
      filter_upwards [hw] with v hv'
      obtain ⟨hvne, -, -, hv⟩ := hv'
      simp only [H, rd_G, hv, zpow_neg]
      have : (v - w₀) ^ ord C x ≠ 0 := zpow_ne_zero _ (sub_ne_zero.mpr hvne)
      field_simp
    rw [dbar_congr heq, dbar_mul (hpow.differentiableAt.restrictScalars ℝ)
      (hgl.differentiableAt (by simp)), hdg, dbar_eq_zero_of_differentiableAt
        hpow.differentiableAt]
    ring
  have hHa := analyticAt_of_dbar_punctured hHs hH0
  have hru : rd u x w₀ = u x := by rw [rd_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  refine ⟨H, hHa, ?_, by simp only [H]; rw [hru], hrel⟩
  simp only [H]
  rw [hru]
  exact mul_ne_zero hK0 (Complex.exp_ne_zero _)

open Classical in
/-- A function with simple pole at `Q₁` (and simple zero at `Q₂`). -/
theorem simplePole_mero (C : FChain X) {u : X → ℂ} (hu : IsSmooth u)
    (hθu : ∀ q : X, ∀ w ∈ (chartAt ℂ q).target, θ C q w = dbar (rd u q) w)
    {Q₁ Q₂ : X} (hQ : Q₁ ≠ Q₂)
    (hord : ∀ v, ord C v = (if v = Q₂ then 1 else 0) - (if v = Q₁ then 1 else 0)) :
    SimplePole (mero C u) Q₁ := by
  classical
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨H, hHa, hH0, hHv, hrel⟩ := mero_local C hu hθu x
    have hm : ord C x = 0 ∨ ord C x = 1 := by
      rw [hord x, if_neg hx]; by_cases h : x = Q₂ <;> simp [h]
    set w₀ := chartAt ℂ x x
    -- `mero` equals `(w - w₀)^m H` on a full neighbourhood
    have hfull : rd (mero C u) x =ᶠ[𝓝 w₀] fun w => (w - w₀) ^ (ord C x).toNat * H w := by
      have hrel' : ∀ᶠ w in 𝓝[≠] w₀,
          rd (mero C u) x w = (w - w₀) ^ (ord C x).toNat * H w := by
        filter_upwards [hrel] with w hw
        rw [hw]
        rcases hm with h | h <;> simp [h]
      rw [eventually_nhdsWithin_iff] at hrel'
      filter_upwards [hrel'] with w hw
      by_cases hw0 : w = w₀
      · rw [hw0, rd_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
        by_cases hxV : x ∈ V C
        · simp only [mero, if_pos hxV]
          rcases hm with h | h
          · have ht : (ord C x).toNat = 0 := by rw [h]; rfl
            rw [if_pos h, ht, pow_zero, one_mul, hHv]
          · have ht : (ord C x).toNat = 1 := by rw [h]; rfl
            rw [if_neg (by rw [h]; norm_num), ht, sub_self, pow_one, zero_mul]
        · have h0 := ord_eq_zero_of_notMem C hxV
          -- off the vertices `mero = G`, and `H(w₀)` is its value
          have ht : (ord C x).toNat = 0 := by rw [h0]; rfl
          simp only [mero, if_neg hxV]
          rw [ht, pow_zero, one_mul, hHv]
          obtain ⟨-, -, hev⟩ := (F_vertex C x).choose_spec
          have hFc : ContinuousAt (rd (F C) x) w₀ :=
            (F_local C (mem_chart_target ℂ x) (by
              rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact hxV)).1.continuousAt
          have hKc : ContinuousAt (F_vertex C x).choose w₀ :=
            ((F_vertex C x).choose_spec.1.self_of_nhds).continuousAt
          have hlim : rd (F C) x w₀ = (F_vertex C x).choose w₀ := by
            have t1 : Tendsto (rd (F C) x) (𝓝[≠] w₀) (𝓝 (rd (F C) x w₀)) :=
              hFc.tendsto.mono_left nhdsWithin_le_nhds
            have t2 : Tendsto (F_vertex C x).choose (𝓝[≠] w₀)
                (𝓝 ((F_vertex C x).choose w₀)) := hKc.tendsto.mono_left nhdsWithin_le_nhds
            refine tendsto_nhds_unique t1 (t2.congr' ?_)
            filter_upwards [hev] with v hv
            have hp : (v - chartAt ℂ x x) ^ (ord C x) = 1 := by rw [h0, zpow_zero]
            rw [hv, hp, one_mul]
          rw [rd_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at hlim
          rw [G, hlim]
      · exact hw hw0
    exact (((analyticAt_id.sub analyticAt_const).pow _).mul hHa).congr hfull.symm
  · obtain ⟨H, hHa, hH0, -, hrel⟩ := mero_local C hu hθu Q₁
    refine ⟨H, hHa, hH0, ?_⟩
    filter_upwards [hrel] with w hw
    rw [hw, hord Q₁, if_neg hQ, if_pos rfl]
    simp

open Classical in
/-- **Abel, two-point form.** A null formal chain from `Q₁` to `Q₂ ≠ Q₁` makes `X` a sphere. -/
theorem homeomorph_of_null_chain [CompactSpace X] [ConnectedSpace X] (C : FChain X)
    {Q₁ Q₂ : X} (hQ : Q₁ ≠ Q₂)
    (hord : ∀ v, ord C v = (if v = Q₂ then 1 else 0) - (if v = Q₁ then 1 else 0))
    (hint : ∀ η : HolomorphicOneForm ℂ X, integral C η = 0) : Nonempty (X ≃ₜ OnePoint ℂ) := by
  obtain ⟨A₀⟩ := exists_discAtlas (X := X)
  set A := A₀.extend fun i : Fin C.length => (C.get i).1.p
  have hA : ∀ c ∈ C, ∃ k, A.p k = c.1.p := by
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hc
    exact ⟨Fin.natAdd A₀.N i, A₀.extend_p _ i⟩
  have horth : ∀ η : HolomorphicOneForm ℂ X,
      A.integral (fun q w => θ C q w * holoF η q w) = 0 := fun η => by
    rw [integral_θ_mul A C hA η, hint η, mul_zero]
  obtain ⟨u, hu, hθu⟩ := dbar_solvable_of_orthogonal A (θ_is01 C) (smoothFam_θ C) horth
  exact (simplePole_mero C hu hθu hQ hord).homeomorph

/-! ### Periods as null chains -/

section Periods

variable [FiniteDimensionalHolomorphicOneForms ℂ X]

/-- Every period is the integral vector of a closed formal chain. -/
theorem exists_closed_fchain {x : Fin (analyticGenus ℂ X) → ℂ}
    (hx : x ∈ genuinePeriodSubgroup X) :
    ∃ Γ : FChain X, (∀ v, ord Γ v = 0) ∧
      ∀ i, integral Γ (holomorphicOneFormFinBasis ℂ X i) = x i := by
  classical
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨P, Q, l₁, l₂, h₁, h₂, rfl⟩ := hy
    refine ⟨fwd l₁ ++ neg (fwd l₂), fun v => ?_, fun i => ?_⟩
    · rw [ord_append, ord_neg, ord_fwd h₁, ord_fwd h₂]; ring
    · rw [integral_append, integral_neg, integral_fwd, integral_fwd]
      show _ = periodVector X l₁ i - periodVector X l₂ i
      rw [sub_eq_add_neg]; rfl
  | zero => exact ⟨[], fun _ => rfl, fun _ => by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨Γ₁, h1, h1'⟩ := hy
    obtain ⟨Γ₂, h2, h2'⟩ := hz
    exact ⟨Γ₁ ++ Γ₂, fun v => by rw [ord_append, h1, h2]; rfl,
      fun i => by rw [integral_append, h1', h2']; rfl⟩
  | neg y _ hy =>
    obtain ⟨Γ, h1, h1'⟩ := hy
    exact ⟨neg Γ, fun v => by rw [ord_neg, h1]; rfl,
      fun i => by rw [integral_neg, h1']; rfl⟩

/-- A chain functional vanishing on a basis vanishes. -/
theorem integral_eq_zero_of_basis (C : FChain X)
    (h : ∀ i, integral C (holomorphicOneFormFinBasis ℂ X i) = 0) (η : HolomorphicOneForm ℂ X) :
    integral C η = 0 := by
  have : integralLM C = 0 := (holomorphicOneFormFinBasis ℂ X).ext fun i => h i
  exact LinearMap.congr_fun this η

/-- **Abel's theorem, two-point separation.** In positive genus, if the period vectors of
chains from `P` to `Q₁` and from `P` to `Q₂` differ by a period, then `Q₁ = Q₂`. -/
theorem eq_of_periodVector_sub_mem [CompactSpace X] [ConnectedSpace X]
    (hg : 0 < analyticGenus ℂ X) {P Q₁ Q₂ : X} {l₁ l₂ : List (ChartSegment X)}
    (h₁ : IsChain l₁ P Q₁) (h₂ : IsChain l₂ P Q₂)
    (hmem : -periodVector X l₁ + periodVector X l₂ ∈ genuinePeriodSubgroup X) : Q₁ = Q₂ := by
  classical
  by_contra hQ
  obtain ⟨Γ, hΓ, hΓi⟩ := exists_closed_fchain hmem
  set C : FChain X := fwd l₂ ++ neg (fwd l₁) ++ neg Γ
  have hord : ∀ v, ord C v = (if v = Q₂ then 1 else 0) - (if v = Q₁ then 1 else 0) := by
    intro v
    simp only [C, ord_append, ord_neg, ord_fwd h₁, ord_fwd h₂, hΓ]
    ring
  have hint : ∀ η, integral C η = 0 := integral_eq_zero_of_basis C fun i => by
    simp only [C, integral_append, integral_neg, integral_fwd, hΓi]
    show _ - _ + -(-periodVector X l₁ i + periodVector X l₂ i) = 0
    simp only [periodVector]
    ring
  obtain ⟨e⟩ := homeomorph_of_null_chain C hQ hord hint
  have e' : X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    e.trans (onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex]))
  have hsub : Subsingleton (HolomorphicOneForm ℂ X) :=
    ⟨fun a b => by rw [holomorphicOneForm_eq_zero_of_homeomorph_sphere a e',
      holomorphicOneForm_eq_zero_of_homeomorph_sphere b e']⟩
  have := analyticGenus_eq_zero_iff_subsingleton.mpr hsub
  omega

end Periods

end FChain

end JacobianChallenge.Surface
