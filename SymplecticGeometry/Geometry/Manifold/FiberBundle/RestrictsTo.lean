/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.StructureGroup
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Descent
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.PartitionOfUnity
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.PartitionOfUnity.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.PartitionOfUnity

/-!
# Forms that restrict to the fibre forms

Let `A` be an atlas of a map `proj : M → B` with model fibre a manifold `F`
(`TauCeti.MapFiber.Atlas`), and let `σ` be a `k`-form on `F`. A `k`-form `τ` on `M`
*restricts to `σ` along `A`* when, for every chart `e` of `A` and every point `b` of its base set,
the pull-back of `τ` along the fibre inclusion `v ↦ e⁻¹ (b, v)` is `σ`. Nothing here needs `σ`
to be symplectic: it may be any form, such as a volume form. For a symplectic fibration, whose
fibre forms are the forms that the charts carry to `σ`, the predicate says that `τ` restricts to
the fibre form on every fibre.

When the coordinate changes of `A` preserve `σ`, that is, when `A` has structure group the
stabilizer `TauCeti.SmoothForm.diffeomorphStabilizer σ`, one chart at each point is enough, and
the predicate passes to every atlas compatible with `A` through that stabilizer: it depends only
on the fibre forms. Conversely, a smooth atlas along which some form restricts to `σ` has that
stabilizer as structure group.

The forms that restrict to `σ` form an affine space: `τ + β` restricts to `σ` exactly when `β`
pulls back to zero on every fibre, as the pull-back `proj^* β` of a form of positive degree on the
base does. This gives Thurston's forms `τ + K proj^* β`.

## Main definitions

* `TauCeti.MapFiber.Atlas.RestrictsTo A σ τ`: the form `τ` on `M` pulls back to `σ` along every
  fibre inclusion of the atlas `A`.
* `TauCeti.MapFiber.Atlas.glueForm A ρ σ`: the form on `M` glued from the pull-backs of a form `σ`
  on `F` along the fibre coordinates of the charts `A.trivAt i`, with the weights `ρ i ∘ proj` of
  a partition of unity `ρ` of the base.

## Main results

* `Bundle.Trivialization.mpullback_fiberInclusionMap_eq_mpullback_coordChange`: the pull-backs of a
  form along the fibre inclusions of two trivializations over a point differ by the coordinate
  change.
* `Bundle.Trivialization.mpullback_fiberInclusionMap_eq_of_mem_diffeomorphStabilizer`: a form that
  one chart pulls back to `σ` over a point is pulled back to `σ` by every chart whose coordinate
  change to the first one preserves `σ`.
* `Bundle.Trivialization.mpullback_fiberInclusionMap_mpullback_snd`: pulling a form on the fibre
  back along the fibre coordinate of a chart and then along its fibre inclusion gives it back.
* `Bundle.Trivialization.apply_eq_of_mpullback_fiberInclusionMap_eq`: two forms with the same
  pull-back to the fibre through `x` agree at `x` on vertical vectors.
* `TauCeti.MapFiber.Atlas.mpullback_snd_trivAt_apply_eq`: when the coordinate changes preserve
  `σ`, the pull-backs of `σ` along the fibre coordinates of any two charts agree on vertical
  vectors.
* `TauCeti.MapFiber.Atlas.RestrictsTo.mpullback_fiberInclusionMap_eq`: along a smooth atlas, the
  smooth pull-back of a form that restricts to `σ` along each fibre inclusion is `σ`.
* `TauCeti.MapFiber.Atlas.RestrictsTo.mextDeriv_apply_eq_zero`: a form that restricts to a closed
  form along a smooth atlas has exterior derivative zero on tuples of vertical vectors.
* `TauCeti.MapFiber.Atlas.RestrictsTo.isClosed`: a form on `F` to which a closed form restricts
  along a smooth atlas over a nonempty base is closed.
* `TauCeti.MapFiber.Atlas.restrictsTo_iff_forall_exists`: for a smooth atlas with structure group
  the stabilizer of `σ`, it suffices that one chart at each point pull `τ` back to `σ`.
* `TauCeti.MapFiber.Atlas.RestrictsTo.of_coordChangeMem`: the predicate passes to an atlas
  compatible with a smooth one through the stabilizer of `σ`.
* `TauCeti.MapFiber.Atlas.RestrictsTo.hasStructureGroup`: a smooth atlas along which a form
  restricts to `σ` has structure group the stabilizer of `σ`.
* `Bundle.Trivialization.mpullback_fiberInclusionMap_mpullback_eq_zero`: the pull-back of a form of
  positive degree on the base vanishes on every fibre, and
  `Bundle.Trivialization.mpullback_fiberInclusionMap_eq_zero_of_isSemibasic`: so does that of a
  form of positive degree semibasic for `proj`.
* `Bundle.Trivialization.smoothForm_mpullback_fiberInclusionMap_mpullback_eq_zero`: the same
  vanishing for the smooth pull-backs of smooth forms.
* `Bundle.Trivialization.mextDeriv_apply_eq_zero_of_mextDeriv_mpullback`: a `C¹` form whose
  pull-back to the fibre through `x` is closed has exterior derivative zero at `x` on tuples of
  vertical vectors. Both vanishing results for the exterior derivative on vertical vectors
  follow from it.
* `Bundle.Trivialization.mextDeriv_apply_eq_zero_of_isSemibasic`: the exterior derivative of a
  `C¹` form of positive degree semibasic for `proj` vanishes on tuples of vertical vectors, as
  its pull-back to each fibre is zero.
* `TauCeti.MapFiber.Atlas.isSmoothForm_glueForm`: along a smooth atlas, with `ρ` subordinate to
  the base sets of the charts, the glued form of a smooth form is smooth.
* `TauCeti.MapFiber.Atlas.glueForm_eq_glueForms`: with `ρ` subordinate to the base sets, the glued
  form is the gluing `SmoothPartitionOfUnity.glueForms` of the pull-backs of `σ`, restricted to
  the sources of the charts.
* `TauCeti.MapFiber.Atlas.mextDeriv_glueForm_apply_of_mem_ker`: on tuples of vertical vectors, the
  exterior derivative of the glued form of `σ` is the glued form of `dσ`.
* `TauCeti.MapFiber.Atlas.mpullback_fiberInclusionMap_glueForm`: along a smooth atlas, the glued
  form pulls back to the fibre over `b'` of a chart as the combination, with the weights at `b'`,
  of the pull-backs of `σ` along the coordinate changes over `b'`.
* `TauCeti.MapFiber.Atlas.restrictsTo_of_apply_eq_sum`: when the coordinate changes preserve `σ`,
  a form that on vertical vectors is a sum of the pull-backs of `σ` along the fibre coordinates of
  the charts, with the weights of a subordinate partition of unity of the base, restricts to `σ`.
  The glued form is one, which gives `TauCeti.MapFiber.Atlas.restrictsTo_glueForm`.
* `TauCeti.MapFiber.Atlas.restrictsTo_add_iff`, `TauCeti.MapFiber.Atlas.RestrictsTo.add_mpullback`
  and `TauCeti.MapFiber.Atlas.convex_setOfPred_restrictsTo`: the affine structure of the forms that
  restrict to `σ`.

## Implementation notes

The predicate is stated with Tau Ceti's rough pull-back `TauCeti.mpullback`, so that it needs no
proof that the fibre inclusions are smooth. The results that compare two fibre inclusions use the
chain rule, and so take the smoothness of the atlas as a hypothesis.

The glued form is smooth by Tau Ceti's `TauCeti.isSmoothForm_sum_finsupport_smul_mpullback`. Its
derivative on vertical vectors comes from the library's
`SmoothPartitionOfUnity.mextDeriv_glueForms_apply_of_mem_ker`, and the naturality of the exterior
derivative, Tau Ceti's `TauCeti.mpullback_mextDeriv_at`.

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
theorem mpullback_fiberInclusionMap_eq_mpullback_coordChange {e e' : Trivialization F proj}
    (he' : e'.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) {b : B}
    (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) (hc : MDifferentiable IF IF (e.coordChange e' b))
    (α : TauCeti.RoughForm IM M V k) :
    TauCeti.mpullback IF IM (e.fiberInclusionMap hb) α =
      TauCeti.mpullback IF IF (e.coordChange e' b)
        (TauCeti.mpullback IF IM (e'.fiberInclusionMap hb') α) := by
  funext v
  rw [e.coe_fiberInclusionMap_eq_comp_coordChange e' hb hb']
  exact TauCeti.mpullback_comp_at (hc v) (mdifferentiable_fiberInclusionMap he' hb' _) α

/-- **Charts related by a stabilizing coordinate change.** If the coordinate change from `e` to
`e'` over `b` is a diffeomorphism `φ` that preserves a form `σ` on the fibre, and a form `α` on
the total space pulls back to `σ` along the fibre inclusion of `e'` over `b`, then `α` pulls back
to `σ` along that of `e` too. -/
theorem mpullback_fiberInclusionMap_eq_of_mem_diffeomorphStabilizer [IsManifold IF 1 F]
    {e e' : Trivialization F proj}
    (he' : e'.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) {b : B}
    (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) {σ : TauCeti.SmoothForm IF F V k}
    {φ : F ≃ₘ⟮IF, IF⟯ F} (hφ : φ ∈ TauCeti.SmoothForm.diffeomorphStabilizer σ)
    (hφe : ⇑φ = e.coordChange e' b) {α : TauCeti.RoughForm IM M V k}
    (h : TauCeti.mpullback IF IM (e'.fiberInclusionMap hb') α = σ.val) :
    TauCeti.mpullback IF IM (e.fiberInclusionMap hb) α = σ.val := by
  rw [e.mpullback_fiberInclusionMap_eq_mpullback_coordChange he' hb hb'
    (hφe ▸ φ.mdifferentiable (by simp)), h, ← hφe]
  exact funext (TauCeti.SmoothForm.mem_diffeomorphStabilizer_iff_forall.1 hφ)

/-- **The fibre coordinate is a left inverse of the fibre inclusion.** For a trivialization `e`
that is differentiable with differentiable inverse, pulling a form on `F` back to `M` along the
fibre coordinate `x ↦ (e x).2`, and then to `F` along the fibre inclusion of `e` over `b`, gives
the form back. -/
theorem mpullback_fiberInclusionMap_mpullback_snd {e : Trivialization F proj}
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) {b : B} (hb : b ∈ e.baseSet)
    (α : TauCeti.RoughForm IF F V k) :
    TauCeti.mpullback IF IM (e.fiberInclusionMap hb)
      (TauCeti.mpullback IM IF (fun x ↦ (e x).2) α) = α := by
  funext v
  have hg : MDifferentiableAt IM IF (fun x ↦ (e x).2) (e.fiberInclusionMap hb v) :=
    mdifferentiableAt_snd.comp _ (he.mdifferentiableAt (e.fiberInclusionMap_mem_source hb v))
  rw [← TauCeti.mpullback_comp_at (mdifferentiable_fiberInclusionMap he hb v) hg,
    (e.leftInverse_snd_fiberInclusionMap hb).comp_eq_id, TauCeti.mpullback_id]

/-- **Forms are determined on vertical vectors by their pull-backs to a fibre.** For a
trivialization `e` that is differentiable with differentiable inverse, two forms on `M` with the
same pull-back along the fibre inclusion of `e` over `proj x` take the same value at `x` on every
tuple of vertical vectors, since the derivative of that fibre inclusion has the vertical space as
range. -/
theorem apply_eq_of_mpullback_fiberInclusionMap_eq {e : Trivialization F proj}
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) {x : M}
    (hx : proj x ∈ e.baseSet) {α β : TauCeti.RoughForm IM M V k}
    (h : TauCeti.mpullback IF IM (e.fiberInclusionMap hx) α =
      TauCeti.mpullback IF IM (e.fiberInclusionMap hx) β)
    {u : Fin k → TangentSpace IM x} (hu : ∀ i, u i ∈ (mfderiv IM IB proj x).ker) :
    α x u = β x u := by
  -- Read `x` as the image of its fibre coordinate under the fibre inclusion; the statement is
  -- generalized over that point, since the tangent vectors depend on it.
  have key : ∀ (y : M) (_ : y = e.fiberInclusionMap hx (e x).2) {u : Fin k → TangentSpace IM y},
      (∀ i, u i ∈ (mfderiv IM IB proj y).ker) → α y u = β y u := by
    rintro y rfl u hu
    have hr := e.range_mfderiv_fiberInclusionMap he hx (e x).2
    choose w hw using fun i ↦ (hr ▸ hu i : u i ∈ LinearMap.range _)
    have hu' : u = fun i ↦ mfderiv IF IM (e.fiberInclusionMap hx) (e x).2 (w i) :=
      funext fun i ↦ (hw i).symm
    rw [hu', ← TauCeti.mpullback_apply, ← TauCeti.mpullback_apply, h]
  exact key x (e.fiberInclusionMap_snd_apply hx).symm hu

/-- **Semibasic forms vanish on the fibres.** The pull-back to a fibre of a form of positive
degree that is semibasic for `proj` is zero, since `proj` is constant on the fibre. No smoothness
is needed (Tau Ceti's `TauCeti.range_mfderiv_le_ker_mfderiv_of_eventually_eq`). -/
theorem mpullback_fiberInclusionMap_eq_zero_of_isSemibasic (e : Trivialization F proj) {b : B}
    (hb : b ∈ e.baseSet) {α : TauCeti.RoughForm IM M V (k + 1)}
    (hα : TauCeti.RoughForm.IsSemibasic IB proj α) :
    TauCeti.mpullback IF IM (e.fiberInclusionMap hb) α = 0 := by
  funext v
  ext w
  rw [TauCeti.mpullback_apply, Pi.zero_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  exact hα.apply_eq_zero _ _ 0 (TauCeti.range_mfderiv_le_ker_mfderiv_of_eventually_eq
    (Filter.Eventually.of_forall (e.proj_fiberInclusionMap hb)) ⟨w 0, rfl⟩)

/-- **Forms from the base vanish on the fibres.** The pull-back to a fibre of the pull-back
`proj^* β` of a form of positive degree on the base is zero, since `proj^* β` is semibasic for
`proj`. No smoothness is needed. -/
theorem mpullback_fiberInclusionMap_mpullback_eq_zero (e : Trivialization F proj) {b : B}
    (hb : b ∈ e.baseSet) (hk : k ≠ 0) (β : TauCeti.RoughForm IB B V k) :
    TauCeti.mpullback IF IM (e.fiberInclusionMap hb) (TauCeti.mpullback IM IB proj β) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  exact e.mpullback_fiberInclusionMap_eq_zero_of_isSemibasic hb
    (TauCeti.RoughForm.isSemibasic_mpullback IB proj β)

/-- **Smooth forms from the base vanish on the fibres.** The smooth pull-back to a fibre of the
smooth pull-back `proj^* β` of a form of positive degree on the base is zero. -/
@[simp]
theorem smoothForm_mpullback_fiberInclusionMap_mpullback_eq_zero [IsManifold IB 1 B]
    [IsManifold IF 1 F] [IsManifold IM 1 M] (e : Trivialization F proj) {b : B}
    (hb : b ∈ e.baseSet) (hι : ContMDiff IF IM ∞ (e.fiberInclusionMap hb)) (hk : k ≠ 0)
    (hproj : ContMDiff IM IB ∞ proj) (β : TauCeti.SmoothForm IB B V k) :
    TauCeti.SmoothForm.mpullback (e.fiberInclusionMap hb) hι
      (TauCeti.SmoothForm.mpullback proj hproj β) = 0 := by
  apply Subtype.ext
  rw [TauCeti.SmoothForm.coe_mpullback, TauCeti.SmoothForm.coe_mpullback,
    e.mpullback_fiberInclusionMap_mpullback_eq_zero hb hk, ZeroMemClass.coe_zero]

/-- **Vertical exterior derivative from the fibres.** Let `e` be a trivialization of `proj` that
is differentiable, with `C²` inverse, and let `α` be a `C¹` form on `M`. If the pull-back of `α`
to the fibre through `x` is closed, then the exterior derivative of `α` vanishes at `x` on every
tuple of vertical vectors: its pull-back to the fibre is the derivative of the pull-back of `α`. -/
theorem mextDeriv_apply_eq_zero_of_mextDeriv_mpullback [IsManifold IF 2 F] [IsManifold IM 2 M]
    {e : Trivialization F proj} (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF))
    (he' : ContMDiffOn (IB.prod IF) IM 2 e.toOpenPartialHomeomorph.symm e.target)
    {α : TauCeti.RoughForm IM M V k}
    (hα' : TauCeti.IsSmoothBundleForm (I := IM) (F := V) (V := Trivial M V) 1 α) {x : M}
    (hx : proj x ∈ e.baseSet)
    (h : TauCeti.mextDeriv (TauCeti.mpullback IF IM (e.fiberInclusionMap hx) α) = 0)
    {u : Fin (k + 1) → TangentSpace IM x} (hu : ∀ i, u i ∈ (mfderiv IM IB proj x).ker) :
    TauCeti.mextDeriv α x u = 0 := by
  have h' : TauCeti.mpullback IF IM (e.fiberInclusionMap hx) (TauCeti.mextDeriv α) =
      TauCeti.mpullback IF IM (e.fiberInclusionMap hx) 0 := by
    rw [TauCeti.mpullback_mextDeriv (e.contMDiff_fiberInclusionMap he' hx) hα', h,
      TauCeti.mpullback_zero]
  exact e.apply_eq_of_mpullback_fiberInclusionMap_eq he hx h' hu

/-- **The derivative of a semibasic form on vertical vectors.** Let `e` be a trivialization of
`proj` that is differentiable, with `C²` inverse. The exterior derivative of a `C¹` form of
positive degree that is semibasic for `proj` vanishes at every point over the base set of `e` on
every tuple of vertical vectors: its pull-back to the fibre is the derivative of the pull-back of
the form, which is zero. -/
theorem mextDeriv_apply_eq_zero_of_isSemibasic [IsManifold IF 2 F] [IsManifold IM 2 M]
    {e : Trivialization F proj} (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF))
    (he' : ContMDiffOn (IB.prod IF) IM 2 e.toOpenPartialHomeomorph.symm e.target)
    {α : TauCeti.RoughForm IM M V (k + 1)} (hα : TauCeti.RoughForm.IsSemibasic IB proj α)
    (hα' : TauCeti.IsSmoothBundleForm (I := IM) (F := V) (V := Trivial M V) 1 α) {x : M}
    (hx : proj x ∈ e.baseSet) {u : Fin (k + 1 + 1) → TangentSpace IM x}
    (hu : ∀ i, u i ∈ (mfderiv IM IB proj x).ker) : TauCeti.mextDeriv α x u = 0 :=
  e.mextDeriv_apply_eq_zero_of_mextDeriv_mpullback he he' hα' hx
    (by rw [e.mpullback_fiberInclusionMap_eq_zero_of_isSemibasic hx hα, TauCeti.mextDeriv_zero])
    hu

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
    TauCeti.mpullback IF IM ((A.trivAt b).fiberInclusionMap hb') τ.val = σ.val

theorem restrictsTo_iff :
    A.RestrictsTo σ τ ↔ ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
      TauCeti.mpullback IF IM ((A.trivAt b).fiberInclusionMap hb') τ.val = σ.val :=
  Iff.rfl

/-- **The smooth pull-back to a fibre.** If `τ` restricts to `σ` along a smooth atlas `A`, then
the smooth pull-back of `τ` along the fibre inclusion `v ↦ (A.trivAt b)⁻¹ (b', v)` of every chart
`A.trivAt b`, over every point `b'` of its base set, is `σ`. -/
theorem RestrictsTo.mpullback_fiberInclusionMap_eq (hA : A.IsContMDiff ∞ IB IF IM)
    (hτ : A.RestrictsTo σ τ) {b b' : B} (hb' : b' ∈ (A.trivAt b).baseSet) :
    SmoothForm.mpullback _
      ((A.trivAt b).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b) hb') τ = σ :=
  (SmoothForm.mpullback_eq_iff _).2 (restrictsTo_iff.1 hτ b b' hb')

/-- **Forms restricting to a closed form are closed on vertical vectors.** If `τ` restricts to a
closed form `σ` along a smooth atlas, then at every point the exterior derivative of `τ` vanishes
on every tuple of vertical vectors: its pull-back to each fibre is the derivative of `σ`. -/
theorem RestrictsTo.mextDeriv_apply_eq_zero [IsManifold IF 2 F] [IsManifold IM 2 M]
    (hA : A.IsContMDiff ∞ IB IF IM) (hτ : A.RestrictsTo σ τ) (hσ : σ.IsClosed) {x : M}
    {u : Fin (k + 1) → TangentSpace IM x} (hu : ∀ i, u i ∈ (mfderiv IM IB proj x).ker) :
    TauCeti.mextDeriv τ.val x u = 0 :=
  (A.trivAt (proj x)).mextDeriv_apply_eq_zero_of_mextDeriv_mpullback
    (hA.mdifferentiable_trivAt (by simp) _) ((hA.contMDiffOn_trivAt_symm _).of_le (by simp))
    ((isSmoothBundleForm_def 1 _).2 (τ.isSmoothForm.of_le (by simp)).contMDiff)
    (A.mem_baseSet_trivAt (proj x))
    (by rw [hτ _ _ (A.mem_baseSet_trivAt (proj x)), (SmoothForm.isClosed_def σ).1 hσ]) hu

/-- **The fibre form of a closed form is closed.** If a closed form `τ` restricts to `σ` along a
smooth atlas over a nonempty base, then `σ` is closed: it is the pull-back of `τ` along a smooth
fibre inclusion. Over an empty base every form `σ` satisfies the hypothesis. -/
theorem RestrictsTo.isClosed [IsManifold IF 2 F] [IsManifold IM 2 M] [Nonempty B]
    (hA : A.IsContMDiff ∞ IB IF IM) (hτ : A.RestrictsTo σ τ) (hτc : τ.IsClosed) :
    σ.IsClosed := by
  obtain ⟨b⟩ := ‹Nonempty B›
  rw [← hτ.mpullback_fiberInclusionMap_eq hA (A.mem_baseSet_trivAt b)]
  exact hτc.mpullback _ _

/-- **One chart at each point suffices.** For a smooth atlas whose coordinate changes preserve
`σ`, a form `τ` restricts to `σ` exactly when, for each point `b'` of the base, some chart whose
base set contains `b'` pulls `τ` back to `σ` over `b'`. -/
theorem restrictsTo_iff_forall_exists (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) :
    A.RestrictsTo σ τ ↔ ∀ b', ∃ b, ∃ hb' : b' ∈ (A.trivAt b).baseSet,
      TauCeti.mpullback IF IM ((A.trivAt b).fiberInclusionMap hb') τ.val = σ.val := by
  refine ⟨fun h b' ↦ ⟨b', A.mem_baseSet_trivAt b', h _ _ _⟩, fun h b b' hb' ↦ ?_⟩
  obtain ⟨b₀, hb₀, h₀⟩ := h b'
  obtain ⟨φ, hφ, hφe⟩ := hasStructureGroup_iff.1 hH b b₀ b' hb' hb₀
  exact Trivialization.mpullback_fiberInclusionMap_eq_of_mem_diffeomorphStabilizer
    (hA.mdifferentiable_trivAt (by simp) b₀) hb' hb₀ hφ hφe h₀

omit [IsManifold IM 1 M] in
/-- **Fibre coordinates of charts with stabilizing coordinate changes.** For a smooth atlas whose
coordinate changes preserve `σ`, the pull-back of `σ` along the fibre coordinate
`x ↦ (A.trivAt b₀ x).2` of a chart pulls back to `σ` along the fibre inclusion of every chart over
every point `b'` of the base set of `A.trivAt b₀`. -/
theorem mpullback_fiberInclusionMap_mpullback_snd_trivAt (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) {b₀ b b' : B}
    (hb₀ : b' ∈ (A.trivAt b₀).baseSet) (hb : b' ∈ (A.trivAt b).baseSet) :
    TauCeti.mpullback IF IM ((A.trivAt b).fiberInclusionMap hb)
      (TauCeti.mpullback IM IF (fun x ↦ (A.trivAt b₀ x).2) σ.val) = σ.val := by
  obtain ⟨φ, hφ, hφe⟩ := hasStructureGroup_iff.1 hH b b₀ b' hb hb₀
  have he₀ := hA.mdifferentiable_trivAt (by simp) b₀
  exact Trivialization.mpullback_fiberInclusionMap_eq_of_mem_diffeomorphStabilizer he₀ hb hb₀ hφ
    hφe ((A.trivAt b₀).mpullback_fiberInclusionMap_mpullback_snd he₀ hb₀ σ.val)

omit [IsManifold IM 1 M] in
/-- **Fibre coordinates of two charts agree on vertical vectors.** For a smooth atlas whose
coordinate changes preserve `σ`, the pull-backs of `σ` along the fibre coordinates of two charts
whose base sets contain `proj x` take the same value at `x` on every tuple of vertical vectors. -/
theorem mpullback_snd_trivAt_apply_eq (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) {b₀ b₁ : B} {x : M}
    (h₀ : proj x ∈ (A.trivAt b₀).baseSet) (h₁ : proj x ∈ (A.trivAt b₁).baseSet)
    {u : Fin k → TangentSpace IM x} (hu : ∀ i, u i ∈ (mfderiv IM IB proj x).ker) :
    TauCeti.mpullback IM IF (fun y ↦ (A.trivAt b₀ y).2) σ.val x u =
      TauCeti.mpullback IM IF (fun y ↦ (A.trivAt b₁ y).2) σ.val x u :=
  (A.trivAt (proj x)).apply_eq_of_mpullback_fiberInclusionMap_eq
    (hA.mdifferentiable_trivAt (by simp) _) (A.mem_baseSet_trivAt _)
    ((mpullback_fiberInclusionMap_mpullback_snd_trivAt hA hH h₀ _).trans
      (mpullback_fiberInclusionMap_mpullback_snd_trivAt hA hH h₁ _).symm) hu

/-- **Independence of the atlas.** If `τ` restricts to `σ` along a smooth atlas `A`, then it
does along every atlas `A'` compatible with `A` through the stabilizer of `σ`. -/
theorem RestrictsTo.of_coordChangeMem (hA : A.IsContMDiff ∞ IB IF IM)
    (h : A.CoordChangeMem A' (SmoothForm.diffeomorphStabilizer σ)) (hτ : A.RestrictsTo σ τ) :
    A'.RestrictsTo σ τ := fun b b' hb' ↦ by
  obtain ⟨φ, hφ, hφe⟩ := coordChangeMem_iff.1 h.symm b b' b' hb' (A.mem_baseSet_trivAt b')
  exact Trivialization.mpullback_fiberInclusionMap_eq_of_mem_diffeomorphStabilizer
    (hA.mdifferentiable_trivAt (by simp) b') hb' (A.mem_baseSet_trivAt b') hφ hφe (hτ _ _ _)

/-- **Restricting forms give atlases with structure group the stabilizer.** If a form
restricts to `σ` along a smooth atlas, the coordinate changes of the atlas preserve `σ`: the
atlas has structure group the stabilizer of `σ`; for a symplectic `σ`, a symplectic atlas. -/
theorem RestrictsTo.hasStructureGroup (hA : A.IsContMDiff ∞ IB IF IM) (hτ : A.RestrictsTo σ τ) :
    A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ) := by
  refine hasStructureGroup_iff.2 fun b b' x hb hb' ↦ ?_
  obtain ⟨φ, -, hφe⟩ := hasStructureGroup_iff.1 hA.hasStructureGroup_top b b' x hb hb'
  refine ⟨φ, SmoothForm.mem_diffeomorphStabilizer_iff_forall.2 fun v ↦ ?_, hφe⟩
  rw [hφe, ← hτ b' x hb', ← (A.trivAt b).mpullback_fiberInclusionMap_eq_mpullback_coordChange
      (hA.mdifferentiable_trivAt (by simp) b') hb hb' (hφe ▸ φ.mdifferentiable (by simp)),
    hτ b x hb, hτ b' x hb']

/-! ### Forms glued from the fibre coordinates -/

section GlueForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable (A) in
/-- The form on `M` glued from a form `σ` on the model fibre by a partition of unity `ρ` of the
base: at `x`, the sum over `i` of `ρ i (proj x)` times the pull-back of `σ` along the fibre
coordinate `y ↦ (A.trivAt i y).2` of the chart `A.trivAt i`. -/
noncomputable def glueForm (ρ : SmoothPartitionOfUnity B IB B univ)
    (σ : TauCeti.RoughForm IF F V k) : TauCeti.RoughForm IM M V k :=
  fun x ↦ ∑ i ∈ ρ.finsupport (proj x),
    ρ i (proj x) • TauCeti.mpullback IM IF (fun y ↦ (A.trivAt i y).2) σ x

omit [IsManifold IF 1 F] [IsManifold IM 1 M] in
theorem glueForm_apply (ρ : SmoothPartitionOfUnity B IB B univ)
    (σ : TauCeti.RoughForm IF F V k) (x : M) :
    glueForm A ρ σ x = ∑ i ∈ ρ.finsupport (proj x),
      ρ i (proj x) • TauCeti.mpullback IM IF (fun y ↦ (A.trivAt i y).2) σ x :=
  (rfl)

omit [IsManifold IF 1 F] [IsManifold IM 1 M] in
/-- **The glued form as a gluing of forms on open sets.** For a partition of unity `ρ` of the
base subordinate to the base sets of the charts, the glued form of `σ` is the gluing
`ρ.glueForms proj` of the restrictions of the pull-backs of `σ` along the fibre coordinates to
the sources of the charts. -/
theorem glueForm_eq_glueForms {ρ : SmoothPartitionOfUnity B IB B univ}
    (hρ : ρ.IsSubordinate fun i ↦ (A.trivAt i).baseSet) (σ : TauCeti.RoughForm IF F V k) :
    glueForm A ρ σ = ρ.glueForms proj (fun i ↦ ⟨(A.trivAt i).source, (A.trivAt i).open_source⟩)
      fun i ↦ TauCeti.mpullback IM IM Subtype.val
        (TauCeti.mpullback IM IF (fun y ↦ (A.trivAt i y).2) σ) := by
  funext x
  rw [glueForm_apply, SmoothPartitionOfUnity.glueForms_apply]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [TauCeti.RoughForm.extendByZeroOfOpens_apply_of_mem _
      ((A.trivAt i).mem_source.2 (hρ.mem_of_mem_finsupport hi)),
    TauCeti.mpullback_subtype_val_apply]

/-- **The derivative of the glued form on vertical vectors.** Along a smooth atlas, for a
partition of unity `ρ` of the base subordinate to the base sets of the charts and a smooth real
form `σ` on the fibre, the exterior derivative of the glued form of `σ` agrees, on tuples of
tangent vectors in the kernel of the differential of `proj`, with the glued form of `dσ`. -/
theorem mextDeriv_glueForm_apply_of_mem_ker [IsManifold IF 2 F] [IsManifold IM 2 M]
    (hA : A.IsContMDiff ∞ IB IF IM)
    {ρ : SmoothPartitionOfUnity B IB B univ}
    (hρ : ρ.IsSubordinate fun i ↦ (A.trivAt i).baseSet) (σ : SmoothForm IF F ℝ k) (x : M)
    {v : Fin (k + 1) → TangentSpace IM x} (hv : ∀ j, v j ∈ (mfderiv IM IB proj x).ker) :
    TauCeti.mextDeriv (glueForm A ρ σ.val) x v = glueForm A ρ (TauCeti.mextDeriv σ.val) x v := by
  have hθ : ∀ i, ∀ y, proj y ∈ (A.trivAt i).baseSet → ContMDiffAt IM
      (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ∞ (fun z ↦ TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) z
        (TauCeti.mpullback IM IF (fun y ↦ (A.trivAt i y).2) σ.val z)) y := fun i y hy ↦
    (σ.contMDiff _).mpullback_form (hA.contMDiffAt_snd_trivAt hy) (by simp)
  rw [glueForm_eq_glueForms hρ, SmoothPartitionOfUnity.mextDeriv_glueForms_apply_of_mem_ker
    (hA.contMDiff_proj.of_le (by simp)) (fun i y hy ↦ (A.trivAt i).mem_source.2 (hρ i hy))
    (fun i ↦ TauCeti.isSmoothForm_mpullback_subtypeVal_of_contMDiffOn fun y hy ↦
      ((hθ i y ((A.trivAt i).mem_source.1 hy)).of_le (by simp)).contMDiffWithinAt) x hv,
    glueForm_apply, ContinuousAlternatingMap.sum_apply]
  calc _ = ∑ i ∈ (ρ.fintsupport (proj x)).attach, ρ i.val (proj x) *
        TauCeti.mpullback IM IF (fun y ↦ (A.trivAt i.val y).2) (TauCeti.mextDeriv σ.val) x v :=
      Finset.sum_congr rfl fun i _ ↦ by
        have hi := hρ i.val ((ρ.mem_fintsupport_iff _ i.val).1 i.property)
        rw [← TauCeti.mpullback_subtypeVal_mextDeriv, TauCeti.mpullback_subtype_val_apply,
          TauCeti.mpullback_mextDeriv_at ((hA.contMDiffAt_snd_trivAt hi).of_le (by simp))
            ((σ.contMDiff _).of_le (by simp))]
        -- The two sides differ only in the point `↑⟨x, _⟩`, which is `x` by definition.
        rfl
    _ = ∑ i ∈ ρ.fintsupport (proj x), ρ i (proj x) *
        TauCeti.mpullback IM IF (fun y ↦ (A.trivAt i y).2) (TauCeti.mextDeriv σ.val) x v :=
      Finset.sum_attach _ fun i ↦ ρ i (proj x) *
        TauCeti.mpullback IM IF (fun y ↦ (A.trivAt i y).2) (TauCeti.mextDeriv σ.val) x v
    _ = _ := by
      refine (Finset.sum_subset (ρ.finsupport_subset_fintsupport _) fun i _ hi ↦ ?_).symm.trans
        (Finset.sum_congr rfl fun i _ ↦ by rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul])
      rw [show ρ i (proj x) = 0 by simpa [ρ.mem_finsupport] using hi, zero_mul]

/-- **The glued form is smooth.** Along a smooth atlas, for a partition of unity of the base
subordinate to the base sets of the charts, the form glued from a smooth form on the fibre is
smooth. -/
theorem isSmoothForm_glueForm [IsManifold IB ∞ B] [IsManifold IF ∞ F] [IsManifold IM ∞ M]
    (hA : A.IsContMDiff ∞ IB IF IM) {ρ : SmoothPartitionOfUnity B IB B univ}
    (hρ : ρ.IsSubordinate fun i ↦ (A.trivAt i).baseSet) (σ : SmoothForm IF F V k) :
    TauCeti.IsSmoothForm IM ∞ (glueForm A ρ σ.val) :=
  TauCeti.isSmoothForm_sum_finsupport_smul_mpullback hρ (fun i ↦ (A.trivAt i).open_baseSet)
    hA.contMDiff_proj (fun _ _ ↦ hA.contMDiffAt_snd_trivAt) σ

omit [IsManifold IF 1 F] [IsManifold IM 1 M] in
/-- **The glued form on a fibre.** Along a smooth atlas, for a partition of unity `ρ` of the base
subordinate to the base sets of the charts, the pull-back of the glued form along the fibre
inclusion of `A.trivAt b` over `b'` is the sum over `i` of `ρ i b'` times the pull-back of `σ`
along the coordinate change from `A.trivAt b` to `A.trivAt i` over `b'`. -/
theorem mpullback_fiberInclusionMap_glueForm (hA : A.IsContMDiff ∞ IB IF IM)
    {ρ : SmoothPartitionOfUnity B IB B univ} (hρ : ρ.IsSubordinate fun i ↦ (A.trivAt i).baseSet)
    (σ : TauCeti.RoughForm IF F V k) {b b' : B} (hb' : b' ∈ (A.trivAt b).baseSet) :
    TauCeti.mpullback IF IM ((A.trivAt b).fiberInclusionMap hb') (glueForm A ρ σ) =
      ∑ i ∈ ρ.finsupport b',
        ρ i b' • TauCeti.mpullback IF IF ((A.trivAt b).coordChange (A.trivAt i) b') σ := by
  set ι := (A.trivAt b).fiberInclusionMap hb'
  -- Each term of the sum is the pull-back along a coordinate change.
  have hterm : ∀ i ∈ ρ.finsupport b',
      TauCeti.mpullback IF IM ι (TauCeti.mpullback IM IF (fun y ↦ (A.trivAt i y).2) σ) =
        TauCeti.mpullback IF IF ((A.trivAt b).coordChange (A.trivAt i) b') σ := fun i hi ↦ by
    have hi' : b' ∈ (A.trivAt i).baseSet := hρ.mem_of_mem_finsupport hi
    have he := hA.mdifferentiable_trivAt (by simp) i
    rw [(A.trivAt b).mpullback_fiberInclusionMap_eq_mpullback_coordChange he hb' hi'
      (((A.trivAt b).contMDiff_coordChange (A.trivAt i) (hA.contMDiffOn_trivAt_symm b)
        (hA.contMDiffOn_trivAt i) hb' hi').mdifferentiable (by simp)),
      (A.trivAt i).mpullback_fiberInclusionMap_mpullback_snd he hi']
  rw [funext (glueForm_apply ρ σ), TauCeti.mpullback_sum_smul]
  funext v
  rw [(A.trivAt b).proj_fiberInclusionMap hb' v, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Pi.smul_apply, ← hterm i hi]

/-- **Weighted sums of fibre coordinates restrict to `σ`.** Along a smooth atlas whose coordinate
changes preserve `σ`, let `ρ` be a partition of unity of the base subordinate to the base sets of
the charts. A form that at each `x`, on every tuple of vertical vectors, is the sum over `c` of
`ρ c (proj x)` times the pull-back of `σ` along the fibre coordinate `y ↦ (A.trivAt c y).2`
restricts to `σ`. Only the values on vertical vectors matter, as they are all that the fibre
inclusions see. -/
theorem restrictsTo_of_apply_eq_sum (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ))
    {ρ : SmoothPartitionOfUnity B IB B univ} (hρ : ρ.IsSubordinate fun c ↦ (A.trivAt c).baseSet)
    (hτ : ∀ (x : M) {u : Fin k → TangentSpace IM x},
      (∀ i, u i ∈ (mfderiv IM IB proj x).ker) → τ.val x u = ∑ c ∈ ρ.fintsupport (proj x),
        ρ c (proj x) * TauCeti.mpullback IM IF (fun y ↦ (A.trivAt c y).2) σ.val x u) :
    A.RestrictsTo σ τ := by
  refine restrictsTo_iff.2 fun b b' hb' ↦ funext fun v ↦ ?_
  ext w
  set j := (A.trivAt b).fiberInclusionMap hb'
  have hp : proj (j v) = b' := (A.trivAt b).proj_fiberInclusionMap hb' v
  have hu : ∀ i, mfderiv IF IM j v (w i) ∈ (mfderiv IM IB proj (j v)).ker := fun i ↦
    TauCeti.range_mfderiv_le_ker_mfderiv_of_eventually_eq
      (Filter.Eventually.of_forall ((A.trivAt b).proj_fiberInclusionMap hb')) ⟨w i, rfl⟩
  -- Each term pulls back to `σ` along `j`, and the weights sum to one.
  have hterm : ∀ c ∈ ρ.fintsupport b', ρ c b' * TauCeti.mpullback IM IF
      (fun y ↦ (A.trivAt c y).2) σ.val (j v) (fun i ↦ mfderiv IF IM j v (w i)) =
        ρ c b' * σ.val v w := fun c hc ↦ by
    rw [← TauCeti.mpullback_apply, mpullback_fiberInclusionMap_mpullback_snd_trivAt hA hH
      (hρ c ((ρ.mem_fintsupport_iff b' c).1 hc)) hb']
  rw [TauCeti.mpullback_apply, hτ _ hu, hp, Finset.sum_congr rfl hterm, ← Finset.sum_mul,
    ρ.sum_finsupport' _ (mem_univ b') (ρ.finsupport_subset_fintsupport _), one_mul]

/-- **The glued form restricts to `σ`.** Along a smooth atlas whose coordinate changes preserve
`σ`, for a partition of unity of the base subordinate to the base sets of the charts, a form
whose values are those of the glued form of `σ` restricts to `σ`. -/
theorem restrictsTo_glueForm (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ))
    {ρ : SmoothPartitionOfUnity B IB B univ} (hρ : ρ.IsSubordinate fun i ↦ (A.trivAt i).baseSet)
    (hτ : τ.val = glueForm A ρ σ.val) : A.RestrictsTo σ τ :=
  restrictsTo_of_apply_eq_sum hA hH hρ fun x u _ ↦ by
    rw [hτ, glueForm_apply, ContinuousAlternatingMap.sum_apply]
    refine Finset.sum_subset (ρ.finsupport_subset_fintsupport _) (fun c _ hc ↦ ?_)
      |>.trans (Finset.sum_congr rfl fun c _ ↦ ?_)
    · rw [ρ.mem_finsupport, mem_support, not_not] at hc
      simp [hc]
    · simp

end GlueForm

/-! ### The affine structure -/

/-- **Adding a form.** If `τ` restricts to `σ`, then `τ + β` does exactly when `β` pulls back to
zero along every fibre inclusion of the atlas. -/
theorem restrictsTo_add_iff (hτ : A.RestrictsTo σ τ) (β : SmoothForm IM M ℝ k) :
    A.RestrictsTo σ (τ + β) ↔ ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
      TauCeti.mpullback IF IM ((A.trivAt b).fiberInclusionMap hb') β.val = 0 := by
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
    (A.trivAt b).mpullback_fiberInclusionMap_mpullback_eq_zero hb' hk, smul_zero]

/-- **Convexity.** The forms that restrict to `σ` along an atlas form a convex set. -/
theorem convex_setOfPred_restrictsTo (A : Atlas F proj) (σ : SmoothForm IF F ℝ k) :
    Convex ℝ {τ : SmoothForm IM M ℝ k | A.RestrictsTo σ τ} := by
  intro τ₁ hτ₁ τ₂ hτ₂ a c _ _ hac b b' hb'
  rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, TauCeti.mpullback_add,
    TauCeti.mpullback_smul, TauCeti.mpullback_smul, hτ₁ b b' hb', hτ₂ b b' hb', ← add_smul, hac,
    one_smul]

end TauCeti.MapFiber.Atlas

end
