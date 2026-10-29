import Jacobian.Periods.RealPeriods
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex
import Jacobian.HolomorphicForms.ChartedSpaceComplexPoints

/-!
# The covering space of primitives; holomorphic forms on a topological sphere vanish

For a holomorphic 1-form `ω` on a Riemann surface `X`, the pairs `(x, a)` of a point and a
value of a local primitive at that point form a covering space `PrimSpace ω → X` (the étalé
space of the sheaf of primitives): it is `X × ℂ`, topologised by the graphs of local
primitives. Over a chart ball `U` with primitive `G`, the map `(x, a) ↦ (x, a - G x)` is a
trivialisation with discrete fibre `ℂ`.

Consequence (via Mathlib's lifting theorem for covering maps): on a simply connected open
set, `ω` has a global primitive. If `X` is homeomorphic to `S²`, then `X` minus any point is
homeomorphic to `ℝ²`, hence simply connected; any two chart chains miss some common point
(Baire), so their integrals agree; by `eq_zero_of_re_chainIntegral_eq`, `ω = 0`.

This proves the direction "homeomorphic to the sphere ⇒ genus 0" of the challenge's
`genus_eq_zero_iff_homeo` without uniformization.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms Set Metric Filter Topology
open scoped Manifold

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  (ω : HolomorphicOneForm ℂ X)

/-! ### Local primitives -/

/-- `G` is a primitive of `ω` on the open set `U`: in the chart at each point of `U`,
`G ∘ c⁻¹` has derivative the chart reading of `ω`. -/
def IsPrim (G : X → ℂ) (U : Set X) : Prop :=
  IsOpen U ∧ ∀ y ∈ U, HasFDerivAt (G ∘ (chartAt ℂ y).symm)
    (chartForm y ω (chartAt ℂ y y)) (chartAt ℂ y y)

/-- **Change of chart** for a local primitive. -/
theorem hasFDerivAt_chartChange {G : X → ℂ} {p q : X} {w : ℂ}
    (hw : w ∈ (chartAt ℂ p).target) (hq : (chartAt ℂ p).symm w ∈ (chartAt ℂ q).source)
    (hG : HasFDerivAt (G ∘ (chartAt ℂ p).symm) (chartForm p ω w) w) :
    HasFDerivAt (G ∘ (chartAt ℂ q).symm)
      (chartForm q ω (chartAt ℂ q ((chartAt ℂ p).symm w)))
      (chartAt ℂ q ((chartAt ℂ p).symm w)) := by
  set x := (chartAt ℂ p).symm w
  set v := chartAt ℂ q x
  have hxp : x ∈ (chartAt ℂ p).source := (chartAt ℂ p).map_target hw
  have hv : v ∈ (chartAt ℂ q).target := (chartAt ℂ q).map_source hq
  have hvx : (chartAt ℂ q).symm v = x := (chartAt ℂ q).left_inv hq
  have hτv : chartMap id q p v = w := by
    show chartAt ℂ p ((chartAt ℂ q).symm v) = w
    rw [hvx]; exact (chartAt ℂ p).right_inv hw
  have hid : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) (id : X → X) := contMDiff_id
  have hτ : HasFDerivAt (chartMap id q p) (fderiv ℂ (chartMap id q p) v) v :=
    (chartMap_differentiableAt hid hv (by rw [hvx]; exact hxp)).hasFDerivAt
  rw [← hτv] at hG
  have hcomp := hG.comp v hτ
  rw [← chartForm_transition ω hv (by rw [hvx]; exact hxp)] at hcomp
  refine hcomp.congr_of_eventuallyEq ?_
  have hcont : ContinuousAt (chartAt ℂ q).symm v := (chartAt ℂ q).continuousAt_symm hv
  filter_upwards [hcont.preimage_mem_nhds ((chartAt ℂ p).open_source.mem_nhds
    (by rw [hvx]; exact hxp))] with z hz
  show G ((chartAt ℂ q).symm z) = G ((chartAt ℂ p).symm (chartAt ℂ p ((chartAt ℂ q).symm z)))
  rw [(chartAt ℂ p).left_inv hz]

/-- A primitive reads correctly in every chart. -/
theorem IsPrim.hasFDerivAt {G : X → ℂ} {U : Set X} (hG : IsPrim ω G U) {y : X} (hy : y ∈ U)
    {q : X} (hq : y ∈ (chartAt ℂ q).source) :
    HasFDerivAt (G ∘ (chartAt ℂ q).symm) (chartForm q ω (chartAt ℂ q y)) (chartAt ℂ q y) := by
  have h := hasFDerivAt_chartChange ω ((chartAt ℂ y).map_source (mem_chart_source ℂ y))
    (by rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]; exact hq) (hG.2 y hy)
  rwa [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)] at h

theorem IsPrim.mono {G : X → ℂ} {U V : Set X} (hG : IsPrim ω G U) (hV : IsOpen V) (hVU : V ⊆ U) :
    IsPrim ω G V :=
  ⟨hV, fun y hy => hG.2 y (hVU hy)⟩

theorem IsPrim.add_const {G : X → ℂ} {U : Set X} (hG : IsPrim ω G U) (c : ℂ) :
    IsPrim ω (fun x => G x + c) U :=
  ⟨hG.1, fun y hy => (hG.2 y hy).add_const c⟩

/-- **Local existence of primitives.** -/
theorem exists_isPrim (x₀ : X) : ∃ U G, x₀ ∈ U ∧ IsPrim ω G U := by
  obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.mp (chartAt ℂ x₀).open_target _
    ((chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀))
  set c := chartAt ℂ x₀
  set H : ℂ → ℂ := fun z => ∫ᶜ t in Path.segment (c x₀) z, chartForm x₀ ω t
  refine ⟨c.source ∩ c ⁻¹' ball (c x₀) ρ, fun x => H (c x),
    ⟨mem_chart_source ℂ x₀, mem_ball_self hρ⟩, c.isOpen_inter_preimage isOpen_ball, ?_⟩
  rintro y ⟨hys, hyb⟩
  have hH : HasFDerivAt (H ∘ c ∘ c.symm) (chartForm x₀ ω (c y)) (c y) := by
    refine (chartForm_hasFDerivAt_primitive x₀ ω hB hyb).congr_of_eventuallyEq ?_
    filter_upwards [c.open_target.mem_nhds (c.map_source hys)] with z hz
    show H (c (c.symm z)) = H z
    rw [c.right_inv hz]
  have h := hasFDerivAt_chartChange ω (G := fun x => H (c x)) (c.map_source hys)
    (by rw [c.left_inv hys]; exact mem_chart_source ℂ y) hH
  rwa [c.left_inv hys] at h

/-- **Two primitives differ by a locally constant function.** -/
theorem IsPrim.eventually_sub_eq {G₁ G₂ : X → ℂ} {U₁ U₂ : Set X} (h₁ : IsPrim ω G₁ U₁)
    (h₂ : IsPrim ω G₂ U₂) {y : X} (hy₁ : y ∈ U₁) (hy₂ : y ∈ U₂) :
    ∀ᶠ y' in 𝓝 y, G₁ y' - G₂ y' = G₁ y - G₂ y := by
  set c := chartAt ℂ y
  set O : Set ℂ := c.target ∩ c.symm ⁻¹' (U₁ ∩ U₂)
  have hO : IsOpen O := c.isOpen_inter_preimage_symm (h₁.1.inter h₂.1)
  have hcy : c y ∈ O := ⟨c.map_source (mem_chart_source ℂ y), by
    show c.symm (c y) ∈ U₁ ∩ U₂
    rw [c.left_inv (mem_chart_source ℂ y)]; exact ⟨hy₁, hy₂⟩⟩
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO _ hcy
  have hD : ∀ w ∈ ball (c y) r,
      HasFDerivAt (fun z => G₁ (c.symm z) - G₂ (c.symm z)) (0 : ℂ →L[ℂ] ℂ) w := by
    intro w hw
    have hwO := hrO hw
    have hs : c.symm w ∈ (chartAt ℂ y).source := c.map_target hwO.1
    have e1 := h₁.hasFDerivAt ω hwO.2.1 hs
    have e2 := h₂.hasFDerivAt ω hwO.2.2 hs
    rw [c.right_inv hwO.1] at e1 e2
    have := e1.sub e2
    rwa [sub_self] at this
  have hnb : ∀ᶠ y' in 𝓝 y, y' ∈ c.source ∧ c y' ∈ ball (c y) r :=
    Filter.Eventually.and (c.open_source.mem_nhds (mem_chart_source ℂ y))
      ((c.continuousAt (mem_chart_source ℂ y)).preimage_mem_nhds
        (isOpen_ball.mem_nhds (mem_ball_self hr)))
  filter_upwards [hnb] with y' hy'
  have := (convex_ball (c y) r).is_const_of_fderivWithin_eq_zero
    (f := fun z => G₁ (c.symm z) - G₂ (c.symm z)) (𝕜 := ℂ)
    (fun w hw => (hD w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => by rw [fderivWithin_of_isOpen isOpen_ball hw]; exact (hD w hw).fderiv)
    hy'.2 (mem_ball_self hr)
  simp only [c.left_inv hy'.1, c.left_inv (mem_chart_source ℂ y)] at this
  exact this

/-! ### The space of primitive values and its covering map -/

/-- Pairs `(x, a)` of a point and a value of a local primitive of `ω` at it. -/
def PrimSpace (_ω : HolomorphicOneForm ℂ X) : Type u := X × ℂ

/-- The graph of a local primitive. -/
def primGraph (G : X → ℂ) (U : Set X) : Set (PrimSpace ω) :=
  {e | e.1 ∈ U ∧ e.2 = G e.1}

instance : TopologicalSpace (PrimSpace ω) :=
  TopologicalSpace.generateFrom {S | ∃ G U, IsPrim ω G U ∧ S = primGraph ω G U}

theorem isOpen_primGraph {G : X → ℂ} {U : Set X} (h : IsPrim ω G U) :
    IsOpen (primGraph ω G U) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨G, U, h, rfl⟩

/-- The point `(x, a)` of the space of primitive values. -/
def primMk (x : X) (a : ℂ) : PrimSpace ω := (x, a)

/-- The projection to `X`. -/
def primProj : PrimSpace ω → X := Prod.fst

/-- Every point lies on the graph of a primitive over a neighbourhood inside any given open
neighbourhood of its base point. -/
theorem exists_primGraph (e : PrimSpace ω) {V : Set X} (hV : IsOpen V) (he : e.1 ∈ V) :
    ∃ G U, IsPrim ω G U ∧ e ∈ primGraph ω G U ∧ U ⊆ V := by
  obtain ⟨U, G, hxU, hG⟩ := exists_isPrim ω e.1
  refine ⟨fun x => G x + (e.2 - G e.1), U ∩ V,
    (hG.add_const ω _).mono ω (hG.1.inter hV) inter_subset_left, ⟨⟨hxU, he⟩, by ring⟩,
    inter_subset_right⟩

theorem continuous_primProj : Continuous (primProj ω) := by
  rw [continuous_def]
  intro V hV
  refine isOpen_iff_forall_mem_open.mpr fun e he => ?_
  obtain ⟨G, U, hG, heG, hUV⟩ := exists_primGraph ω e hV he
  exact ⟨primGraph ω G U, fun e' he' => hUV he'.1, isOpen_primGraph ω hG, heG⟩

/-- The section `x ↦ (x, G x + c)` over the domain of a primitive is continuous. -/
theorem continuousAt_primSection {G : X → ℂ} {U : Set X} (hG : IsPrim ω G U) (c : ℂ) {y : X}
    (hy : y ∈ U) : ContinuousAt (fun x : X => primMk ω x (G x + c)) y := by
  unfold ContinuousAt
  rw [TopologicalSpace.tendsto_nhds_generateFrom_iff]
  intro S hS hmem
  obtain ⟨(G' : X → ℂ), (U' : Set X), hG', rfl⟩ := hS
  obtain ⟨hyU', hval⟩ : y ∈ U' ∧ G y + c = G' y := hmem
  filter_upwards [hG'.1.mem_nhds hyU', hG'.eventually_sub_eq ω hG hyU' hy] with x hxU' hsub
  refine ⟨hxU', ?_⟩
  show G x + c = G' x
  have hval' : G y + c = G' y := hval
  linear_combination hval' - hsub

/-- `ℂ` with the discrete topology: the fibre of the space of primitive values. -/
def DiscreteComplex : Type := ℂ

instance : TopologicalSpace DiscreteComplex := ⊥

instance : DiscreteTopology DiscreteComplex := ⟨rfl⟩

/-- The trivialisation of the space of primitive values over the domain of a primitive. -/
noncomputable def trivOfPrim {G : X → ℂ} {U : Set X} (hG : IsPrim ω G U) :
    Bundle.Trivialization DiscreteComplex (primProj ω) where
  toFun e := (e.1, (show DiscreteComplex from e.2 - G e.1))
  invFun b := primMk ω b.1 (G b.1 + (show ℂ from b.2))
  source := primProj ω ⁻¹' U
  target := U ×ˢ univ
  map_source' e he := ⟨he, mem_univ _⟩
  map_target' b hb := hb.1
  left_inv' e _ := by
    show ((e.1, G e.1 + (e.2 - G e.1)) : X × ℂ) = e
    ext <;> simp
  right_inv' b _ := by
    show ((b.1, (show DiscreteComplex from G b.1 + (show ℂ from b.2) - G b.1)) :
      X × DiscreteComplex) = b
    ext
    · rfl
    · show G b.1 + (show ℂ from b.2) - G b.1 = (show ℂ from b.2)
      ring
  open_source := hG.1.preimage (continuous_primProj ω)
  open_target := hG.1.prod isOpen_univ
  continuousOn_toFun := by
    intro e he
    refine ContinuousAt.continuousWithinAt ?_
    refine (continuous_primProj ω).continuousAt.prodMk ?_
    set c : ℂ := e.2 - G e.1
    have hmem : e ∈ primGraph ω (fun x => G x + c) U := ⟨he, by simp [c]⟩
    refine (continuousAt_const (y := (show DiscreteComplex from c))).congr ?_
    filter_upwards [(isOpen_primGraph ω (hG.add_const ω c)).mem_nhds hmem] with e' he'
    show c = e'.2 - G e'.1
    rw [he'.2]; ring
  continuousOn_invFun := by
    rintro ⟨y, d⟩ ⟨hy, -⟩
    refine ContinuousAt.continuousWithinAt ?_
    have hs := (continuousAt_primSection ω hG (show ℂ from d) hy).comp
      (continuous_fst.continuousAt (x := ((y, d) : X × DiscreteComplex)))
    refine hs.congr ?_
    filter_upwards [(isOpen_univ.prod (isOpen_discrete {d})).mem_nhds
      (show ((y, d) : X × DiscreteComplex) ∈ univ ×ˢ {d} from ⟨mem_univ _, rfl⟩)] with b hb
    obtain ⟨-, hb2⟩ := hb
    rw [mem_singleton_iff] at hb2
    show primMk ω b.1 (G b.1 + (show ℂ from d)) = primMk ω b.1 (G b.1 + (show ℂ from b.2))
    rw [hb2]
  baseSet := U
  open_baseSet := hG.1
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- **The space of primitive values is a covering space.** -/
theorem isCoveringMap_primProj : IsCoveringMap (primProj ω) := by
  choose U G hx hG using exists_isPrim ω
  exact IsCoveringMap.mk (F := fun _ => DiscreteComplex) (e := fun x => trivOfPrim ω (hG x))
    (h := hx)

/-! ### Global primitives on simply connected open sets -/

/-- **On a simply connected open set, `ω` has a primitive.** (Lift the inclusion through the
covering space of primitive values.) -/
theorem exists_isPrim_of_simplyConnected {W : Set X} (hW : IsOpen W) [SimplyConnectedSpace W]
    (hne : W.Nonempty) : ∃ Φ : X → ℂ, IsPrim ω Φ W := by
  classical
  haveI : LocPathConnectedSpace X := ChartedSpace.locPathConnectedSpace ℂ X
  haveI : LocPathConnectedSpace W := hW.locPathConnectedSpace
  obtain ⟨w₀, hw₀⟩ := hne
  let f : C(W, X) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨F, ⟨-, hFp⟩, -⟩ := (isCoveringMap_primProj ω).existsUnique_continuousMap_lifts f
    ⟨w₀, hw₀⟩ (primMk ω w₀ 0) rfl
  have hF1 : ∀ w : W, (F w).1 = w := fun w => congrFun hFp w
  let Φ : X → ℂ := fun x => if h : x ∈ W then (F ⟨x, h⟩).2 else 0
  refine ⟨Φ, hW, fun y hy => ?_⟩
  obtain ⟨U, G, hyU, hG⟩ := exists_isPrim ω y
  set c : ℂ := Φ y - G y
  have hS : IsOpen (primGraph ω (fun x => G x + c) U) := isOpen_primGraph ω (hG.add_const ω c)
  have hFy : F ⟨y, hy⟩ ∈ primGraph ω (fun x => G x + c) U := by
    refine ⟨by rw [hF1]; exact hyU, ?_⟩
    rw [hF1]
    show (F ⟨y, hy⟩).2 = G y + (Φ y - G y)
    simp [Φ, hy]
  have hpre : F ⁻¹' primGraph ω (fun x => G x + c) U ∈ 𝓝 (⟨y, hy⟩ : W) :=
    F.continuous.continuousAt.preimage_mem_nhds (hS.mem_nhds hFy)
  rw [nhds_subtype_eq_comap, Filter.mem_comap] at hpre
  obtain ⟨t, ht, hts⟩ := hpre
  have hev : Φ =ᶠ[𝓝 y] fun x => G x + c := by
    filter_upwards [ht, hW.mem_nhds hy] with x hxt hxW
    have hx := hts (show (⟨x, hxW⟩ : W).1 ∈ t from hxt)
    have h2 := hx.2
    rw [hF1] at h2
    simp only [Φ, hxW, dif_pos]
    exact h2
  have hd := (hG.add_const ω c).2 y hyU
  refine hd.congr_of_eventuallyEq ?_
  have hcont : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
    (chartAt ℂ y).continuousAt_symm ((chartAt ℂ y).map_source (mem_chart_source ℂ y))
  rw [← (chartAt ℂ y).left_inv (mem_chart_source ℂ y)] at hev
  exact hcont.eventually hev

/-- A segment of a chart chain whose image lies in the domain of a primitive integrates to
the difference of the primitive at its ends. -/
theorem IsPrim.segment_integral {Φ : X → ℂ} {W : Set X} (hΦ : IsPrim ω Φ W)
    (s : ChartSegment X) (hs : ∀ t ∈ segment ℝ s.a s.b, (chartAt ℂ s.p).symm t ∈ W) :
    s.integral ω = Φ s.stop - Φ s.start := by
  set c := chartAt ℂ s.p
  set K := segment ℝ s.a s.b
  have hKb : K ⊆ ball s.center s.radius :=
    (convex_ball _ _).segment_subset s.a_mem s.b_mem
  have hK : IsCompact K := by
    show IsCompact (segment ℝ s.a s.b)
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  set O : Set ℂ := ball s.center s.radius ∩ c.symm ⁻¹' W
  have hO : IsOpen O := by
    have h1 : IsOpen (c.target ∩ c.symm ⁻¹' W) := c.isOpen_inter_preimage_symm hΦ.1
    have h2 : ball s.center s.radius ∩ (c.target ∩ c.symm ⁻¹' W) = O := by
      ext z; constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, s.ball_subset h1, h3⟩
    rw [← h2]; exact isOpen_ball.inter h1
  have hKO : K ⊆ O := fun t ht => ⟨hKb ht, hs t ht⟩
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_thickening_subset_open hO hKO
  set V := Metric.thickening δ K
  have hV : IsOpen V := isOpen_thickening
  have hVc : Convex ℝ V := (convex_segment _ _).thickening δ
  set H : ℂ → ℂ := fun z => ∫ᶜ t in Path.segment s.center z, chartForm s.p ω t
  have hD : ∀ w ∈ V, HasFDerivAt (fun z => Φ (c.symm z) - H z) (0 : ℂ →L[ℂ] ℂ) w := by
    intro w hw
    have hwO := hδO hw
    have hwt : w ∈ c.target := s.ball_subset hwO.1
    have e1 := hΦ.hasFDerivAt ω hwO.2 (c.map_target hwt)
    rw [c.right_inv hwt] at e1
    have e2 := chartForm_hasFDerivAt_primitive s.p ω s.ball_subset hwO.1
    have := e1.sub e2
    rwa [sub_self] at this
  have hconst := hVc.is_const_of_fderivWithin_eq_zero (f := fun z => Φ (c.symm z) - H z)
    (𝕜 := ℂ) (fun w hw => (hD w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => by rw [fderivWithin_of_isOpen hV hw]; exact (hD w hw).fderiv)
    (self_subset_thickening hδ K (right_mem_segment ℝ s.a s.b))
    (self_subset_thickening hδ K (left_mem_segment ℝ s.a s.b))
  rw [ChartSegment.integral_eq_sub]
  show H s.b - H s.a = Φ (c.symm s.b) - Φ (c.symm s.a)
  linear_combination -hconst

/-- A chain whose segments lie in the domain of a primitive integrates to the difference of
the primitive at its ends. -/
theorem IsPrim.chainIntegral_eq {Φ : X → ℂ} {W : Set X} (hΦ : IsPrim ω Φ W)
    {l : List (ChartSegment X)} {P Q : X} (hl : IsChain l P Q)
    (hs : ∀ s ∈ l, ∀ t ∈ segment ℝ s.a s.b, (chartAt ℂ s.p).symm t ∈ W) :
    chainIntegral ω l = Φ Q - Φ P := by
  induction l generalizing P with
  | nil =>
    simp only [isChain_nil] at hl
    subst hl; simp
  | cons s l ih =>
    obtain ⟨h1, h2⟩ := hl
    rw [chainIntegral_cons, hΦ.segment_integral ω s (hs s (List.mem_cons_self ..)),
      ih h2 (fun s' hs' => hs s' (List.mem_cons_of_mem _ hs')), ← h1]
    ring

/-! ### Avoiding finitely many segments -/

/-- A segment in `ℂ` has empty interior. -/
theorem interior_segment_complex (a b : ℂ) : interior (segment ℝ a b) = ∅ := by
  by_contra hne
  obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior w hw
  have hsub : ball w ε ⊆ segment ℝ a b := hball.trans interior_subset
  set d := b - a
  -- on the segment, `((z - a) * conj d).im = 0`
  have hline : ∀ z ∈ segment ℝ a b, ((z - a) * (starRingEnd ℂ) d).im = 0 := by
    intro z hz
    rw [segment_eq_image'] at hz
    obtain ⟨t, -, rfl⟩ := hz
    rw [add_sub_cancel_left, Complex.real_smul, mul_assoc, Complex.mul_conj]
    simp [Complex.mul_im]
  by_cases hd : d = 0
  · have hab : b = a := by rw [← sub_eq_zero]; exact hd
    have h1 := hsub (mem_ball_self hε)
    have h2 := hsub (show w + (ε / 2 : ℝ) ∈ ball w ε by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith)
    rw [hab, segment_same, mem_singleton_iff] at h1 h2
    have : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination h2 - h1
    have : ε / 2 = 0 := by exact_mod_cast this
    linarith
  · have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd
    set v : ℂ := Complex.I * ((ε / 2 / ‖d‖ : ℝ) : ℂ) * d
    have hv : ‖v‖ = ε / 2 := by
      simp only [v, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show 0 < ε / 2 / ‖d‖ by positivity)]
      field_simp
    have h1 := hline w (hsub (mem_ball_self hε))
    have h2 := hline (w + v) (hsub (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hv]; linarith))
    have hcalc : ((w + v - a) * (starRingEnd ℂ) d).im =
        ((w - a) * (starRingEnd ℂ) d).im + ε / 2 / ‖d‖ * Complex.normSq d := by
      have : (v * (starRingEnd ℂ) d).im = ε / 2 / ‖d‖ * Complex.normSq d := by
        simp only [v]
        rw [mul_assoc, Complex.mul_conj]
        simp [Complex.mul_im, Complex.mul_re]
      rw [show (w + v - a) * (starRingEnd ℂ) d =
        (w - a) * (starRingEnd ℂ) d + v * (starRingEnd ℂ) d by ring, Complex.add_im, this]
    rw [hcalc, h1] at h2
    have : 0 < ε / 2 / ‖d‖ * Complex.normSq d :=
      mul_pos (by positivity) (Complex.normSq_pos.mpr hd)
    linarith

/-- **Finitely many chart segments miss some point.** (Baire: otherwise one segment image
would contain an open set, and so would the segment in its chart.) -/
theorem exists_not_mem_segments [T2Space X] [CompactSpace X] [Nonempty X]
    (L : List (ChartSegment X)) :
    ∃ z : X, ∀ s ∈ L, ∀ t ∈ segment ℝ s.a s.b, (chartAt ℂ s.p).symm t ≠ z := by
  by_contra hcon
  push Not at hcon
  let K : Fin L.length → Set X := fun i =>
    (chartAt ℂ (L.get i).p).symm '' segment ℝ (L.get i).a (L.get i).b
  have hsegT : ∀ s : ChartSegment X, segment ℝ s.a s.b ⊆ (chartAt ℂ s.p).target := fun s =>
    ((convex_ball _ _).segment_subset s.a_mem s.b_mem).trans s.ball_subset
  have hKc : ∀ i, IsClosed (K i) := by
    intro i
    have hseg : IsCompact (segment ℝ (L.get i).a (L.get i).b) := by
      rw [segment_eq_image_lineMap]
      exact isCompact_Icc.image AffineMap.lineMap_continuous
    exact (hseg.image_of_continuousOn
      ((chartAt ℂ (L.get i).p).continuousOn_symm.mono (hsegT _))).isClosed
  have hU : ⋃ i, K i = univ := by
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨s, hs, t, ht, hzt⟩ := hcon z
    subst hzt
    obtain ⟨i, rfl⟩ := List.get_of_mem hs
    exact mem_iUnion.mpr ⟨i, t, ht, rfl⟩
  obtain ⟨i, y, hy⟩ := nonempty_interior_of_iUnion_of_closed hKc hU
  set s := L.get i
  set c := chartAt ℂ s.p
  have hyK : y ∈ K i := interior_subset hy
  obtain ⟨t₀, ht₀, rfl⟩ := hyK
  have hsrc : c.symm t₀ ∈ c.source := c.map_target (hsegT s ht₀)
  have hopen : IsOpen (c '' (c.source ∩ interior (K i))) :=
    c.isOpen_image_source_inter isOpen_interior
  have hsubseg : c '' (c.source ∩ interior (K i)) ⊆ segment ℝ s.a s.b := by
    rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    obtain ⟨t, ht, rfl⟩ := interior_subset hx
    rw [c.right_inv (hsegT s ht)]
    exact ht
  have hmem : c (c.symm t₀) ∈ interior (segment ℝ s.a s.b) :=
    interior_mono hsubseg (hopen.subset_interior_iff.mpr subset_rfl
      ⟨c.symm t₀, ⟨hsrc, hy⟩, rfl⟩)
  rw [interior_segment_complex] at hmem
  exact hmem

/-! ### Forms on a topological sphere -/

/-- A surface homeomorphic to `S²`, minus a point, is simply connected (it is homeomorphic to
`ℝ²` by stereographic projection). -/
theorem simplyConnectedSpace_compl_of_homeomorph_sphere
    (e : X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (z : X) :
    SimplyConnectedSpace ({z}ᶜ : Set X) := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  set σ := stereographic' 2 (e z)
  have h1 : ({z}ᶜ : Set X) ≃ₜ σ.source := by
    refine (e.image {z}ᶜ).trans (Homeomorph.setCongr ?_)
    rw [stereographic'_source, Homeomorph.image_compl, Set.image_singleton]
  have h2 : σ.source ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    σ.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target (e z))).trans (Homeomorph.Set.univ _))
  exact (h1.trans h2).toHomotopyEquiv.simplyConnectedSpace

/-- **A holomorphic 1-form on a compact Riemann surface homeomorphic to `S²` vanishes.** -/
theorem holomorphicOneForm_eq_zero_of_homeomorph_sphere [T2Space X] [CompactSpace X]
    [ConnectedSpace X] (e : X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ω = 0 := by
  refine eq_zero_of_re_chainIntegral_eq ω fun P Q l₁ l₂ h₁ h₂ => ?_
  obtain ⟨z, hz⟩ := exists_not_mem_segments (l₁ ++ l₂)
  haveI := simplyConnectedSpace_compl_of_homeomorph_sphere e z
  have hne : ({z}ᶜ : Set X).Nonempty := by
    obtain ⟨p, q, hpq⟩ := HolomorphicForms.exists_two_distinct_points_of_chartedSpaceComplex
      (X := X)
    by_cases hp : p = z
    · exact ⟨q, fun hq => hpq (hp.trans hq.symm)⟩
    · exact ⟨p, hp⟩
  obtain ⟨Φ, hΦ⟩ := exists_isPrim_of_simplyConnected ω isOpen_compl_singleton hne
  rw [hΦ.chainIntegral_eq ω h₁ fun s hs t ht => hz s (List.mem_append_left _ hs) t ht,
    hΦ.chainIntegral_eq ω h₂ fun s hs t ht => hz s (List.mem_append_right _ hs) t ht]

end JacobianChallenge.Periods
