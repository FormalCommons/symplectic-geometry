/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.StructureGroup
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Forms that restrict to the fibre forms

Let `A` be an atlas of a map `proj : M → B` with model fibre a manifold `F`
(`TauCeti.MapFiber.Atlas`), and let `σ` be a `k`-form on `F`. A `k`-form `τ` on `M`
*restricts to `σ` along `A`* when, for every chart `e` of `A` and every point `b` of its base set,
the pull-back of `τ` along the fibre inclusion `v ↦ e⁻¹ (b, v)` is `σ`. For a symplectic
fibration, whose fibre forms are the forms that the charts carry to `σ`, this says that `τ`
restricts to the fibre form on every fibre.

When the coordinate changes of `A` preserve `σ`, that is, when `A` has structure group the
stabilizer `TauCeti.SmoothForm.diffeomorphStabilizer σ`, one chart at each point is enough, and
the predicate passes to every atlas compatible with `A` through that stabilizer: it depends only
on the fibre forms. Conversely, a smooth atlas along which some form restricts to `σ` has that
stabilizer as structure group.

The forms that restrict to `σ` form an affine space: `τ + β` restricts to `σ` exactly when `β`
pulls back to zero on every fibre, as the pull-back `proj^* β` of a form of positive degree on the
base does. This gives Thurston's forms `τ + K proj^* β`.

A two-form `τ` is *vertically nondegenerate* for `proj` when it is nondegenerate on the kernel of
the derivative of `proj` at every point. For a smooth atlas, with `M` finite-dimensional,
that kernel is the image of the tangent space of the fibre, so a form that restricts to a
nondegenerate `σ` is vertically nondegenerate, and a vertically nondegenerate form pulls back to a
nondegenerate form along every fibre inclusion.

## Main definitions

* `TauCeti.MapFiber.Atlas.RestrictsTo A σ τ`: the form `τ` on `M` pulls back to `σ` along every
  fibre inclusion of the atlas `A`.
* `TauCeti.SmoothTwoForm.IsVerticallyNondegenerate IB proj τ`: the form `τ` is nondegenerate on
  the kernel of the derivative of `proj` at every point.

## Main results

* `Bundle.Trivialization.mpullback_fiberInclusion_eq_mpullback_coordChange`: the pull-backs of a
  form along the fibre inclusions of two trivializations over a point differ by the coordinate
  change.
* `Bundle.Trivialization.mpullback_fiberInclusion_eq_of_mem_diffeomorphStabilizer`: a form that
  one chart pulls back to `σ` over a point is pulled back to `σ` by every chart whose coordinate
  change to the first one preserves `σ`.
* `TauCeti.MapFiber.Atlas.restrictsTo_iff_forall_exists`: for a smooth atlas with structure group
  the stabilizer of `σ`, it suffices that one chart at each point pull `τ` back to `σ`.
* `TauCeti.MapFiber.Atlas.RestrictsTo.of_coordChangeMem`: the predicate passes to an atlas
  compatible with a smooth one through the stabilizer of `σ`.
* `TauCeti.MapFiber.Atlas.RestrictsTo.hasStructureGroup`: a smooth atlas along which a form
  restricts to `σ` has structure group the stabilizer of `σ`.
* `Bundle.Trivialization.mpullback_fiberInclusion_mpullback_eq_zero`: the pull-back of a form of
  positive degree on the base vanishes on every fibre.
* `TauCeti.MapFiber.Atlas.restrictsTo_add_iff`, `TauCeti.MapFiber.Atlas.RestrictsTo.add_mpullback`
  and `TauCeti.MapFiber.Atlas.convex_setOf_restrictsTo`: the affine structure of the forms that
  restrict to `σ`.
* `Bundle.Trivialization.nondegenerate_restrict_ker_mfderiv_iff_separatingLeft`: at a point of a
  fibre of a differentiable trivialization, a two-form is nondegenerate on the kernel of the
  derivative of `proj` exactly when its pull-back to the fibre is nondegenerate there.
* `TauCeti.MapFiber.Atlas.RestrictsTo.isVerticallyNondegenerate`: along a smooth atlas, a form
  that restricts to a nondegenerate form is vertically nondegenerate.
* `TauCeti.SmoothTwoForm.IsVerticallyNondegenerate.isNondegenerate_mpullback_fiberInclusion`: a
  vertically nondegenerate form pulls back to a nondegenerate form along the fibre inclusions of a
  smooth trivialization.

## Implementation notes

The predicate is stated with Tau Ceti's rough pull-back `TauCeti.mpullback`, so that it needs no
proof that the fibre inclusions are smooth. The results that compare two fibre inclusions use the
chain rule, and so take the smoothness of the atlas as a hypothesis.

The results on vertically nondegenerate forms identify the kernel of the derivative of `proj` with
the image of the derivative of a fibre inclusion by
`Bundle.Trivialization.range_mfderiv_fiberInclusion`, and so assume that `M` is
finite-dimensional.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1 (Definition 6.1.2 and the proof of Theorem 6.1.4).
* [W. P. Thurston, *Some simple examples of symplectic manifolds*][Thurston1976].
-/

public section

open Bundle Function Set
open scoped Manifold ContDiff

/-! ### Fibre inclusions and pull-backs -/

namespace Bundle.Trivialization

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {proj : M → B} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

/-- **Fibre inclusions through two charts.** If `e'` is differentiable with differentiable
inverse and the coordinate change from `e` to `e'` over `b` is differentiable, then the pull-back
of a form along the fibre inclusion of `e` over `b` is the pull-back, along that coordinate
change, of its pull-back along the fibre inclusion of `e'`. -/
theorem mpullback_fiberInclusion_eq_mpullback_coordChange {e e' : Trivialization F proj}
    (he' : e'.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) {b : B}
    (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) (hc : MDifferentiable IF IF (e.coordChange e' b))
    (α : TauCeti.RoughForm IM M V k) :
    TauCeti.mpullback IF IM (e.fiberInclusion hb) α =
      TauCeti.mpullback IF IF (e.coordChange e' b)
        (TauCeti.mpullback IF IM (e'.fiberInclusion hb') α) := by
  have h : ⇑(e.fiberInclusion hb) = e'.fiberInclusion hb' ∘ e.coordChange e' b :=
    funext fun v ↦ (e.fiberInclusion_coordChange e' hb hb' v).symm
  funext v
  rw [h]
  exact TauCeti.mpullback_comp_at (hc v) (mdifferentiable_fiberInclusion he' hb' _) α

/-- **Charts related by a stabilizing coordinate change.** If the coordinate change from `e` to
`e'` over `b` is a diffeomorphism `φ` that preserves a form `σ` on the fibre, and a form `α` on
the total space pulls back to `σ` along the fibre inclusion of `e'` over `b`, then `α` pulls back
to `σ` along that of `e` too. -/
theorem mpullback_fiberInclusion_eq_of_mem_diffeomorphStabilizer [IsManifold IF 1 F]
    {e e' : Trivialization F proj}
    (he' : e'.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) {b : B}
    (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) {σ : TauCeti.SmoothForm IF F V k}
    {φ : F ≃ₘ⟮IF, IF⟯ F} (hφ : φ ∈ TauCeti.SmoothForm.diffeomorphStabilizer σ)
    (hφe : ⇑φ = e.coordChange e' b) {α : TauCeti.RoughForm IM M V k}
    (h : TauCeti.mpullback IF IM (e'.fiberInclusion hb') α = σ.val) :
    TauCeti.mpullback IF IM (e.fiberInclusion hb) α = σ.val := by
  rw [e.mpullback_fiberInclusion_eq_mpullback_coordChange he' hb hb'
    (hφe ▸ φ.mdifferentiable (by simp)), h, ← hφe]
  exact funext (TauCeti.SmoothForm.mem_diffeomorphStabilizer_iff_forall.1 hφ)

/-- **Forms from the base vanish on the fibres.** The pull-back to a fibre of the pull-back
`proj^* β` of a form of positive degree on the base is zero, since `proj` is constant on the
fibre. No smoothness is needed: where one of the two maps is not differentiable, its derivative is
zero. -/
theorem mpullback_fiberInclusion_mpullback_eq_zero (e : Trivialization F proj) {b : B}
    (hb : b ∈ e.baseSet) (hk : k ≠ 0) (β : TauCeti.RoughForm IB B V k) :
    TauCeti.mpullback IF IM (e.fiberInclusion hb) (TauCeti.mpullback IM IB proj β) = 0 := by
  funext v
  by_cases hι : MDifferentiableAt IF IM (e.fiberInclusion hb) v
  · by_cases hproj : MDifferentiableAt IM IB proj (e.fiberInclusion hb v)
    · rw [← TauCeti.mpullback_comp_at hι hproj,
        show proj ∘ e.fiberInclusion hb = fun _ ↦ b from funext (e.proj_fiberInclusion hb),
        TauCeti.mpullback_const hk]
    · refine TauCeti.mpullback_apply_eq_zero ?_
      ext w
      rw [TauCeti.mpullback_apply, mfderiv_zero_of_not_mdifferentiableAt hproj]
      exact (β _).map_coord_zero ⟨0, Nat.pos_of_ne_zero hk⟩ (zero_apply _)
  · ext w
    rw [TauCeti.mpullback_apply, mfderiv_zero_of_not_mdifferentiableAt hι]
    exact (TauCeti.mpullback IM IB proj β _).map_coord_zero ⟨0, Nat.pos_of_ne_zero hk⟩
      (zero_apply _)

/-- **Two-forms on the tangent spaces of a fibre.** Let `e` be a trivialization of `proj` that is
differentiable with differentiable inverse, `M` being finite-dimensional. A two-form `τ` on `M` is
nondegenerate on the kernel of the derivative of `proj` at the point `e.fiberInclusion hb v`
exactly when its pull-back along the fibre inclusion of `e` over `b` is nondegenerate at `v`. -/
theorem nondegenerate_restrict_ker_mfderiv_iff_separatingLeft [IsManifold IF ∞ F]
    [IsManifold IM ∞ M] [FiniteDimensional ℝ EM] {e : Trivialization F proj}
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) {b : B}
    (hb : b ∈ e.baseSet) (hι : ContMDiff IF IM ∞ (e.fiberInclusion hb))
    (τ : TauCeti.SmoothTwoForm IM M) (v : F) :
    ((τ.bilinFormAt (e.fiberInclusion hb v)).restrict
        (mfderiv IM IB proj (e.fiberInclusion hb v)).ker).Nondegenerate ↔
      ((TauCeti.SmoothForm.mpullback (e.fiberInclusion hb) hι τ).bilinFormAt v).SeparatingLeft := by
  have hrange := e.range_mfderiv_fiberInclusion he hb v
  have hpull : ∀ u w, (TauCeti.SmoothForm.mpullback (e.fiberInclusion hb) hι τ).bilinFormAt v u w =
      τ.bilinFormAt _ (mfderiv IF IM (e.fiberInclusion hb) v u)
        (mfderiv IF IM (e.fiberInclusion hb) v w) := fun u w ↦ by
    rw [TauCeti.SmoothForm.bilinFormAt_apply, TauCeti.SmoothForm.eval₂_mpullback,
      TauCeti.SmoothForm.bilinFormAt_apply]
  have hrefl : ((τ.bilinFormAt (e.fiberInclusion hb v)).restrict
      (mfderiv IM IB proj (e.fiberInclusion hb v)).ker).IsRefl :=
    (TauCeti.SmoothForm.isAlt_bilinFormAt τ _).isRefl.domRestrict _
  refine hrefl.nondegenerate_iff_separatingLeft.trans ⟨fun h u hu ↦ ?_, fun h ⟨u, hu⟩ hw ↦ ?_⟩
  · refine (injective_iff_map_eq_zero _).1 (e.injective_mfderiv_fiberInclusion he hb v) u <|
      congrArg Subtype.val (h ⟨_, hrange ▸ LinearMap.mem_range_self _ u⟩ fun ⟨w, hw⟩ ↦ ?_)
    rw [← hrange] at hw
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hw
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      Submodule.coe_mk, Submodule.coe_mk, ContinuousLinearMap.coe_coe, ← hpull]
    exact hu w
  · have hu' := hu
    rw [← hrange] at hu'
    obtain ⟨u', rfl⟩ := LinearMap.mem_range.1 hu'
    refine Subtype.ext ?_
    rw [Submodule.coe_mk, Submodule.coe_zero, h u' fun w ↦ ?_, map_zero]
    rw [hpull]
    exact hw ⟨_, hrange ▸ LinearMap.mem_range_self _ w⟩

end Bundle.Trivialization

/-! ### Forms that restrict to a form on the fibre -/

namespace TauCeti.MapFiber.Atlas

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  [IsManifold IF 1 F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM 1 M]
  {proj : M → B} {A A' : Atlas F proj} {k : ℕ} {σ : SmoothForm IF F ℝ k} {τ : SmoothForm IM M ℝ k}

/-- A form `τ` on the total space *restricts to* the form `σ` on the model fibre along the atlas
`A` when, for every chart `A.trivAt b` and every point `b'` of its base set, the pull-back of `τ`
along the fibre inclusion `v ↦ (A.trivAt b)⁻¹ (b', v)` is `σ`. -/
def RestrictsTo (A : Atlas F proj) (σ : SmoothForm IF F ℝ k) (τ : SmoothForm IM M ℝ k) : Prop :=
  ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
    TauCeti.mpullback IF IM ((A.trivAt b).fiberInclusion hb') τ.val = σ.val

theorem restrictsTo_iff :
    A.RestrictsTo σ τ ↔ ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
      TauCeti.mpullback IF IM ((A.trivAt b).fiberInclusion hb') τ.val = σ.val :=
  Iff.rfl

/-- **One chart at each point suffices.** For a smooth atlas whose coordinate changes preserve
`σ`, a form `τ` restricts to `σ` exactly when, for each point `b'` of the base, some chart whose
base set contains `b'` pulls `τ` back to `σ` over `b'`. -/
theorem restrictsTo_iff_forall_exists (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) :
    A.RestrictsTo σ τ ↔ ∀ b', ∃ b, ∃ hb' : b' ∈ (A.trivAt b).baseSet,
      TauCeti.mpullback IF IM ((A.trivAt b).fiberInclusion hb') τ.val = σ.val := by
  refine ⟨fun h b' ↦ ⟨b', A.mem_baseSet_trivAt b', h _ _ _⟩, fun h b b' hb' ↦ ?_⟩
  obtain ⟨b₀, hb₀, h₀⟩ := h b'
  obtain ⟨φ, hφ, hφe⟩ := hasStructureGroup_iff.1 hH b b₀ b' hb' hb₀
  exact Trivialization.mpullback_fiberInclusion_eq_of_mem_diffeomorphStabilizer
    (hA.mdifferentiable_trivAt (by simp) b₀) hb' hb₀ hφ hφe h₀

/-- **Independence of the atlas.** If `τ` restricts to `σ` along a smooth atlas `A`, then it
does along every atlas `A'` compatible with `A` through the stabilizer of `σ`. -/
theorem RestrictsTo.of_coordChangeMem (hA : A.IsContMDiff ∞ IB IF IM)
    (h : A.CoordChangeMem A' (SmoothForm.diffeomorphStabilizer σ)) (hτ : A.RestrictsTo σ τ) :
    A'.RestrictsTo σ τ := fun b b' hb' ↦ by
  obtain ⟨φ, hφ, hφe⟩ := coordChangeMem_iff.1 h.symm b b' b' hb' (A.mem_baseSet_trivAt b')
  exact Trivialization.mpullback_fiberInclusion_eq_of_mem_diffeomorphStabilizer
    (hA.mdifferentiable_trivAt (by simp) b') hb' (A.mem_baseSet_trivAt b') hφ hφe (hτ _ _ _)

/-- **Restricting forms give symplectic atlases.** If a form restricts to `σ` along a smooth
atlas, the coordinate changes of the atlas preserve `σ`: the atlas has structure group the
stabilizer of `σ`. -/
theorem RestrictsTo.hasStructureGroup (hA : A.IsContMDiff ∞ IB IF IM) (hτ : A.RestrictsTo σ τ) :
    A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ) := by
  refine hasStructureGroup_iff.2 fun b b' x hb hb' ↦ ?_
  obtain ⟨φ, -, hφe⟩ := hasStructureGroup_iff.1 hA.hasStructureGroup_top b b' x hb hb'
  refine ⟨φ, SmoothForm.mem_diffeomorphStabilizer_iff_forall.2 fun v ↦ ?_, hφe⟩
  rw [hφe, ← hτ b' x hb', ← (A.trivAt b).mpullback_fiberInclusion_eq_mpullback_coordChange
      (hA.mdifferentiable_trivAt (by simp) b') hb hb' (hφe ▸ φ.mdifferentiable (by simp)),
    hτ b x hb, hτ b' x hb']

/-! ### The affine structure -/

/-- **Adding a form.** If `τ` restricts to `σ`, then `τ + β` does exactly when `β` pulls back to
zero along every fibre inclusion of the atlas. -/
theorem restrictsTo_add_iff (hτ : A.RestrictsTo σ τ) (β : SmoothForm IM M ℝ k) :
    A.RestrictsTo σ (τ + β) ↔ ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
      TauCeti.mpullback IF IM ((A.trivAt b).fiberInclusion hb') β.val = 0 := by
  refine forall₃_congr fun b b' hb' ↦ ?_
  rw [Submodule.coe_add, TauCeti.mpullback_add, hτ b b' hb', add_eq_left]

/-- **Thurston's forms.** If `τ` restricts to `σ`, `k ≠ 0` and `proj` is smooth, then
`τ + K proj^* β` restricts to `σ` for every form `β` of degree `k` on the base and every real
`K`. -/
theorem RestrictsTo.add_mpullback [IsManifold IB 1 B] (hτ : A.RestrictsTo σ τ) (hk : k ≠ 0)
    (hproj : ContMDiff IM IB ∞ proj) (β : SmoothForm IB B ℝ k) (K : ℝ) :
    A.RestrictsTo σ (τ + K • SmoothForm.mpullback proj hproj β) := by
  refine (restrictsTo_add_iff hτ _).2 fun b b' hb' ↦ ?_
  rw [Submodule.coe_smul, SmoothForm.coe_mpullback, TauCeti.mpullback_smul,
    (A.trivAt b).mpullback_fiberInclusion_mpullback_eq_zero hb' hk, smul_zero]

/-- **Convexity.** The forms that restrict to `σ` along an atlas form a convex set. -/
theorem convex_setOf_restrictsTo (A : Atlas F proj) (σ : SmoothForm IF F ℝ k) :
    Convex ℝ {τ : SmoothForm IM M ℝ k | A.RestrictsTo σ τ} := by
  intro τ₁ hτ₁ τ₂ hτ₂ a c _ _ hac b b' hb'
  rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, TauCeti.mpullback_add,
    TauCeti.mpullback_smul, TauCeti.mpullback_smul, hτ₁ b b' hb', hτ₂ b b' hb', ← add_smul, hac,
    one_smul]

end TauCeti.MapFiber.Atlas

/-! ### Vertically nondegenerate two-forms -/

namespace TauCeti.SmoothTwoForm

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] (IB : ModelWithCorners ℝ EB HB) {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  [IsManifold IF ∞ F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM ∞ M]
  {proj : M → B} {τ : SmoothTwoForm IM M}

/-- A two-form `τ` on `M` is *vertically nondegenerate* for a map `proj : M → B` when, at every
point `x`, its restriction to the vertical space, the kernel of the derivative of `proj` at `x`,
is nondegenerate. For a map with a smooth atlas and a finite-dimensional `M`, it implies
that `τ` pulls back to a nondegenerate form on every fibre. -/
def IsVerticallyNondegenerate (proj : M → B) (τ : SmoothTwoForm IM M) : Prop :=
  ∀ x, ((τ.bilinFormAt x).restrict (mfderiv IM IB proj x).ker).Nondegenerate

variable {IB}

theorem isVerticallyNondegenerate_iff :
    IsVerticallyNondegenerate IB proj τ ↔
      ∀ x, ((τ.bilinFormAt x).restrict (mfderiv IM IB proj x).ker).Nondegenerate :=
  Iff.rfl

/-- Vertical nondegeneracy in terms of vectors: a vertical vector on which `τ` pairs to zero with
every vertical vector is zero. One side suffices, since `τ` is alternating. -/
theorem isVerticallyNondegenerate_iff_forall :
    IsVerticallyNondegenerate IB proj τ ↔
      ∀ x, ∀ u ∈ (mfderiv IM IB proj x).ker,
        (∀ w ∈ (mfderiv IM IB proj x).ker, τ.bilinFormAt x u w = 0) → u = 0 := by
  refine forall_congr' fun x ↦ ?_
  have hrefl : ((τ.bilinFormAt x).restrict (mfderiv IM IB proj x).ker).IsRefl :=
    (SmoothForm.isAlt_bilinFormAt τ x).isRefl.domRestrict _
  refine hrefl.nondegenerate_iff_separatingLeft.trans ?_
  exact ⟨fun h u hu hw ↦ congrArg Subtype.val (h ⟨u, hu⟩ fun w ↦ hw w w.property),
    fun h u hu ↦ Subtype.ext (h u u.property fun w hw ↦ hu ⟨w, hw⟩)⟩

/-- **The fibres of a vertically nondegenerate form.** Let `e` be a trivialization of `proj`
that is smooth with smooth inverse, `M` being finite-dimensional. If `τ` is vertically
nondegenerate, then its pull-back along each fibre inclusion of `e` is a nondegenerate form on the
model fibre. -/
theorem IsVerticallyNondegenerate.isNondegenerate_mpullback_fiberInclusion
    [FiniteDimensional ℝ EM] (hτ : IsVerticallyNondegenerate IB proj τ)
    {e : Trivialization F proj} (he : ContMDiffOn IM (IB.prod IF) ∞ e e.source)
    (he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target) {b : B}
    (hb : b ∈ e.baseSet) :
    IsNondegenerate
      (SmoothForm.mpullback (e.fiberInclusion hb) (e.contMDiff_fiberInclusion he_symm hb) τ) := by
  have hd : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF) :=
    ⟨he.mdifferentiableOn (by simp), he_symm.mdifferentiableOn (by simp)⟩
  rw [isNondegenerate_iff_separatingLeft]
  intro v u hu
  exact (e.nondegenerate_restrict_ker_mfderiv_iff_separatingLeft hd hb _ τ v).1
    (isVerticallyNondegenerate_iff.1 hτ _) u
    fun w ↦ by rw [SmoothForm.bilinFormAt_apply]; exact hu w

end TauCeti.SmoothTwoForm

namespace TauCeti.MapFiber.Atlas

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  [IsManifold IF ∞ F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM ∞ M]
  {proj : M → B} {A : Atlas F proj} {σ : SmoothTwoForm IF F} {τ : SmoothTwoForm IM M}

/-- **Restricting forms are vertically nondegenerate.** If a two-form `τ` restricts to a
nondegenerate form `σ` along a smooth atlas of `proj`, with `M` finite-dimensional, then
`τ` is vertically nondegenerate: the vertical space at each point is the image of the tangent
space of the fibre. -/
theorem RestrictsTo.isVerticallyNondegenerate [FiniteDimensional ℝ EM]
    (hA : A.IsContMDiff ∞ IB IF IM) (hσ : σ.IsNondegenerate) (hτ : A.RestrictsTo σ τ) :
    SmoothTwoForm.IsVerticallyNondegenerate IB proj τ := by
  refine SmoothTwoForm.isVerticallyNondegenerate_iff.2 fun x ↦ ?_
  have hb := A.mem_baseSet_trivAt (proj x)
  have hx : (A.trivAt (proj x)).fiberInclusion hb (A.trivAt (proj x) x).2 = x := by
    rw [Trivialization.fiberInclusion_apply,
      (A.trivAt (proj x)).symm_apply_mk_proj ((A.trivAt (proj x)).mem_source.2 hb)]
  have hι := (A.trivAt (proj x)).contMDiff_fiberInclusion (hA.contMDiffOn_trivAt_symm _) hb
  have hpull : SmoothForm.mpullback _ hι τ = σ :=
    Subtype.ext ((SmoothForm.coe_mpullback _ hι τ).trans (hτ _ _ hb))
  refine hx ▸ ((A.trivAt (proj x)).nondegenerate_restrict_ker_mfderiv_iff_separatingLeft
    (hA.mdifferentiable_trivAt (by simp) _) hb hι τ _).2 ?_
  rw [hpull]
  exact fun u hu ↦ SmoothTwoForm.isNondegenerate_iff_separatingLeft.1 hσ _ u
    fun w ↦ by rw [← SmoothForm.bilinFormAt_apply]; exact hu w

end TauCeti.MapFiber.Atlas

end
