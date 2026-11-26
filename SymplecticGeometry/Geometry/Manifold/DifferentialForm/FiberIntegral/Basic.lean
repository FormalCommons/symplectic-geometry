/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.Basic
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.StructureGroup
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.FiberBundle.MapFiber
public import TauCeti.Geometry.Manifold.Orientation.Preserving
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.Naturality
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The fibre integral of a fibration with an atlas

Let `proj : M → B` be a map with model fibre `F` and `e` a trivialization of it. For a form `α` of
degree `r + m` on `M`, a point `b` of the base set of `e` and tangent vectors `v₁, …, vᵣ` at `b`,
the form `Bundle.Trivialization.fiberIntegrand e α b v` of degree `m` on `F` is the integrand of
the fibre integral read through `e`: the pull-back of `α` along the inverse of `e`, a form on
`B × F`, has the integrand `SymplecticGeometry.prodFiberIntegrand` over `b`. At `y` it sends `w`
to the value of `α` at `e⁻¹ (b, y)` on the images of `(v₁, 0), …, (vᵣ, 0), (0, w₁), …, (0, wₘ)`
under the derivative of `e⁻¹`, so it is the pull-back along the fibre inclusion
`y ↦ e⁻¹ (b, y)` of `α` with its first `r` arguments set to lifts of the `vᵢ`. For an atlas
`A : TauCeti.MapFiber.Atlas F proj` the integrand `TauCeti.MapFiber.Atlas.fiberIntegrand A α b v`
is the one read through the chart `A.trivAt b`. Both are linear in `α`, and multilinear and
alternating in `v`, as `prodFiberIntegrand` is.

On an open set `U` of the base set of `e`, the integrand over a point of `U` is that of the
product `U × F` for the pull-back of `α` along `(b, y) ↦ e⁻¹ (b, y)`
(`Bundle.Trivialization.fiberIntegrand_eq_prodFiberIntegrand`); this reduces the fibre integral
of a fibration to that of a product, by `SymplecticGeometry.prodFiberIntegrand_mpullback_prodMap`
along the inclusion of `U`.

The integrand does not depend on the lifts of the base vectors
(`Bundle.Trivialization.fiberIntegrand_apply_of_lift`): any tangent vectors `Xᵢ y` of `M` at
`e⁻¹ (b, y)` that `proj` sends to `vᵢ` may replace the images of `(vᵢ, 0)`. They differ from them
by vectors in the kernel of the derivative of `proj`, which is the image of the derivative of the
fibre inclusion (`Bundle.Trivialization.range_mfderiv_fiberInclusionMap`), a space of dimension
at most `m` that contains the last `m` arguments. An alternating map of `r + m` vectors does not
see such changes (`ContinuousAlternatingMap.map_append_add_of_mem`).

In degree `m` (`r = 0`) the integrand is the pull-back of `α` along the fibre inclusion
(`Bundle.Trivialization.fiberIntegrand_degree_zero`).

Two trivializations over a common point `b` give integrands that differ by the pull-back along
the coordinate change between them over `b`
(`Bundle.Trivialization.fiberIntegrand_eq_mpullback_coordChange`): the coordinate change on
`B × F` covers the identity of `B`, so `SymplecticGeometry.prodFiberIntegrand_mpullback_of_fst_eq`
applies to it. For an atlas whose coordinate changes preserve an orientation `o` of `F`, change
of variables along these diffeomorphisms of `F`
(`Topology.IsOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt`) shows that
the integral over `F` of the integrand does not depend on the chart that reads it
(`TauCeti.MapFiber.Atlas.integralTopForm_fiberIntegrand_trivAt`).

For a smooth atlas whose coordinate changes preserve `o`, with `F` compact and Hausdorff and `B`
boundaryless, the fibre integral `TauCeti.MapFiber.Atlas.fiberIntegral A hA ho` sends a smooth
form `α` of degree `r + m` on `M` to the `r`-form on `B` whose value at `b` on `v` is the integral
over `F` of `A.fiberIntegrand α b v`. On the base set `U` of a chart `e` of the atlas, the
integrand over every point is read through `e` without changing its integral, so the restriction
of the fibre integral to `U` is the fibre integral `SymplecticGeometry.prodFiberIntegral` on
`U × F` of the pull-back of `α` along `(b, y) ↦ e⁻¹ (b, y)`
(`TauCeti.MapFiber.Atlas.mpullback_subtype_val_fiberIntegral`); the fibre integral is therefore
smooth, smoothness of a form being local (`TauCeti.contMDiffAt_mpullback_subtype_val_iff`).

## Main definitions

* `Bundle.Trivialization.fiberIntegrand e α b v`: the integrand read through `e`.
* `TauCeti.MapFiber.Atlas.fiberIntegrand A α b v`: the integrand read through `A.trivAt b`.
* `TauCeti.MapFiber.Atlas.fiberIntegral A hA ho`: the fibre integral of an oriented atlas.

## Main results

* `Bundle.Trivialization.fiberIntegrand_apply`, `TauCeti.MapFiber.Atlas.fiberIntegrand_apply`:
  the value of the integrand on tangent vectors of `F`.
* `Bundle.Trivialization.fiberIntegrand_add` and its neighbours: linearity in `α`;
  `Bundle.Trivialization.fiberIntegrand_update_add`,
  `Bundle.Trivialization.fiberIntegrand_update_smul` and
  `Bundle.Trivialization.fiberIntegrand_eq_zero_of_eq`: multilinearity and alternation in `v`;
  the same for `TauCeti.MapFiber.Atlas.fiberIntegrand`.
* `Bundle.Trivialization.fiberIntegrand_eq_prodFiberIntegrand`,
  `TauCeti.MapFiber.Atlas.fiberIntegrand_eq_prodFiberIntegrand`: the integrand as that of a
  product.
* `Bundle.Trivialization.fiberIntegrand_apply_of_lift`,
  `TauCeti.MapFiber.Atlas.fiberIntegrand_apply_of_lift`: independence of the lifts.
* `Bundle.Trivialization.fiberIntegrand_degree_zero`,
  `TauCeti.MapFiber.Atlas.fiberIntegrand_degree_zero`: the integrand in degree `m`.
* `Bundle.Trivialization.fiberIntegrand_eq_mpullback_coordChange`: the integrands read through
  two trivializations differ by the coordinate change.
* `TauCeti.MapFiber.Atlas.integralTopForm_fiberIntegrand_trivAt`: for an oriented atlas, the
  integral of the integrand does not depend on the chart.
* `TauCeti.MapFiber.Atlas.isSmoothForm_fiberIntegrand`: the integrand of a smooth form is smooth.
* `TauCeti.MapFiber.Atlas.fiberIntegral_apply`: the value of the fibre integral.
* `TauCeti.MapFiber.Atlas.mpullback_subtype_val_fiberIntegral`: the restriction of the fibre
  integral to the base set of a chart is a fibre integral on a product.
* `TauCeti.MapFiber.Atlas.fiberIntegral_apply_of_mem`,
  `TauCeti.MapFiber.Atlas.fiberIntegral_apply_of_lift`: the value through any
  chart at `b`, and through any lifts of the base vectors.
* `TauCeti.MapFiber.Atlas.fiberIntegral_apply_zero`: in degree `m`, the integral over each fibre.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6.
-/

public section

noncomputable section

open Set Function Bundle
open scoped Manifold ContDiff

variable {E H E' H' EM HM B F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace F] [ChartedSpace H' F]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {proj : M → B} {r m : ℕ}

namespace Bundle.Trivialization

open SymplecticGeometry TauCeti

variable (e : Trivialization F proj)

/-- **The integrand of the fibre integral, read through a trivialization.** For a form `α` of
degree `r + m` on `M`, a point `b : B` and tangent vectors `v₁, …, vᵣ` at `b`, the form of degree
`m` on `F` whose value at `y` sends `w` to the value of `α` at `e⁻¹ (b, y)` on the images of
`(v₁, 0), …, (vᵣ, 0), (0, w₁), …, (0, wₘ)` under the derivative of `e⁻¹`: the integrand over `b`
of the pull-back of `α` to `B × F` along `e⁻¹`. It is the integrand of the fibre over `b` when `b`
lies in the base set of `e`. -/
def fiberIntegrand (α : RoughForm IM M ℝ (r + m)) (b : B) (v : Fin r → TangentSpace I b) :
    RoughForm J F ℝ m :=
  prodFiberIntegrand (mpullback (I.prod J) IM e.toOpenPartialHomeomorph.symm α) b v

theorem fiberIntegrand_def (α : RoughForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) :
    e.fiberIntegrand (J := J) α b v =
      prodFiberIntegrand (mpullback (I.prod J) IM e.toOpenPartialHomeomorph.symm α) b v :=
  (rfl)

/-- The value of the integrand at `y` on `w` is that of `α` at `e⁻¹ (b, y)` on the images of
`(v₁, 0), …, (vᵣ, 0), (0, w₁), …, (0, wₘ)` under the derivative of `e⁻¹` at `(b, y)`. -/
@[simp]
theorem fiberIntegrand_apply (α : RoughForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) (y : F) (w : Fin m → TangentSpace J y) :
    e.fiberIntegrand α b v y w = α (e.toOpenPartialHomeomorph.symm (b, y)) (fun p ↦
      mfderiv (I.prod J) IM e.toOpenPartialHomeomorph.symm (b, y)
        ((Manifold.tangentSpaceProdEquiv (b, y)).symm
          (Fin.append (fun i ↦ (v i, 0)) (fun j ↦ (0, w j)) p))) := by
  rw [fiberIntegrand_def, prodFiberIntegrand_apply, mpullback_apply]

/-- The integrand is additive in the form. -/
@[simp]
theorem fiberIntegrand_add (α β : RoughForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) :
    e.fiberIntegrand (J := J) (α + β) b v = e.fiberIntegrand α b v + e.fiberIntegrand β b v := by
  simp only [fiberIntegrand_def, mpullback_add, prodFiberIntegrand_add]

/-- The integrand is homogeneous in the form. -/
@[simp]
theorem fiberIntegrand_smul (c : ℝ) (α : RoughForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) :
    e.fiberIntegrand (J := J) (c • α) b v = c • e.fiberIntegrand α b v := by
  simp only [fiberIntegrand_def, mpullback_smul, prodFiberIntegrand_smul]

/-- The integrand of the zero form is zero. -/
@[simp]
theorem fiberIntegrand_zero (b : B) (v : Fin r → TangentSpace I b) :
    e.fiberIntegrand (J := J) (0 : RoughForm IM M ℝ (r + m)) b v = 0 := by
  simp only [fiberIntegrand_def, mpullback_zero, prodFiberIntegrand_zero]

/-- The integrand of `-α` is minus that of `α`. -/
@[simp]
theorem fiberIntegrand_neg (α : RoughForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) :
    e.fiberIntegrand (J := J) (-α) b v = -e.fiberIntegrand α b v := by
  rw [← neg_one_smul ℝ α, fiberIntegrand_smul, neg_one_smul]

/-- The integrand is subtractive in the form. -/
@[simp]
theorem fiberIntegrand_sub (α β : RoughForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) :
    e.fiberIntegrand (J := J) (α - β) b v = e.fiberIntegrand α b v - e.fiberIntegrand β b v := by
  simp only [fiberIntegrand_def, mpullback_sub, prodFiberIntegrand_sub]

/-- The integrand is additive in each base vector `v i`. -/
theorem fiberIntegrand_update_add [DecidableEq (Fin r)] (α : RoughForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) (i : Fin r) (x x' : TangentSpace I b) :
    e.fiberIntegrand (J := J) α b (update v i (x + x')) =
      e.fiberIntegrand α b (update v i x) + e.fiberIntegrand α b (update v i x') :=
  prodFiberIntegrand_update_add _ b v i x x'

/-- The integrand is homogeneous in each base vector `v i`. -/
theorem fiberIntegrand_update_smul [DecidableEq (Fin r)] (α : RoughForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) (i : Fin r) (c : ℝ) (x : TangentSpace I b) :
    e.fiberIntegrand (J := J) α b (update v i (c • x)) =
      c • e.fiberIntegrand α b (update v i x) :=
  prodFiberIntegrand_update_smul _ b v i c x

/-- The integrand vanishes when two base vectors are equal. -/
theorem fiberIntegrand_eq_zero_of_eq (α : RoughForm IM M ℝ (r + m)) (b : B)
    {v : Fin r → TangentSpace I b} {i j : Fin r} (hv : v i = v j) (hij : i ≠ j) :
    e.fiberIntegrand (J := J) α b v = 0 :=
  prodFiberIntegrand_eq_zero_of_eq _ b hv hij

/-- **The integrand as that of a product.** Let `U` be an open set of `B` inside the base set of
`e`, on which the inverse of `e` is differentiable. Over a point `b` of `U`, the integrand read
through `e` is the integrand over `b` of the pull-back of `α` to `U × F` along
`(b, y) ↦ e⁻¹ (b, y)`. -/
theorem fiberIntegrand_eq_prodFiberIntegrand
    (he : MDifferentiableOn (I.prod J) IM e.toOpenPartialHomeomorph.symm e.target)
    {U : TopologicalSpace.Opens B} (hU : (U : Set B) ⊆ e.baseSet) (α : RoughForm IM M ℝ (r + m))
    (b : U) (v : Fin r → TangentSpace I b) :
    e.fiberIntegrand (I := I) α b v = prodFiberIntegrand
      (mpullback (I.prod J) IM (fun p : U × F ↦ e.toOpenPartialHomeomorph.symm (p.1, p.2)) α) b v
    := by
  have hval : MDifferentiableAt I I (Subtype.val : U → B) b :=
    contMDiff_subtypeVal.mdifferentiableAt one_ne_zero
  have hf (y : F) : MDifferentiableAt (I.prod J) (I.prod J) (Prod.map (Subtype.val : U → B) id)
      (b, y) := ((contMDiff_subtypeVal.prodMap contMDiff_id).mdifferentiableAt one_ne_zero)
  have hg (y : F) :
      MDifferentiableAt (I.prod J) IM e.toOpenPartialHomeomorph.symm ((b : B), y) :=
    (he _ (e.mem_target.2 (hU b.property))).mdifferentiableAt
      (e.open_target.mem_nhds (e.mem_target.2 (hU b.property)))
  have hcomp : (fun p : U × F ↦ e.toOpenPartialHomeomorph.symm (p.1, p.2)) =
      e.toOpenPartialHomeomorph.symm ∘ Prod.map Subtype.val id := rfl
  symm
  funext y
  rw [prodFiberIntegrand_def, hcomp, mpullback_comp_at (hf y) (hg y), ← prodFiberIntegrand_def,
    prodFiberIntegrand_mpullback_prodMap hval]
  simp only [Manifold.mfderiv_subtype_val_apply]
  exact congrFun (e.fiberIntegrand_def (J := J) α (b : B) v).symm y

/-- **The integrand does not depend on the lifts.** Let `e` be differentiable with differentiable
inverse, `b` a point of its base set, and let the model space of `F` have dimension at most `m`.
For tangent vectors `Xᵢ y` of `M` at `e⁻¹ (b, y)` that the derivative of `proj` sends to `vᵢ`,
the integrand at `y` sends `w` to the value of `α` at `e⁻¹ (b, y)` on `X₁ y, …, Xᵣ y` followed by
the images of `w₁, …, wₘ` under the derivative of the fibre inclusion `y ↦ e⁻¹ (b, y)`. No
regularity in `y` is asked of the `Xᵢ`. -/
theorem fiberIntegrand_apply_of_lift [FiniteDimensional ℝ E']
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (I.prod J)) {b : B} (hb : b ∈ e.baseSet)
    (hm : Module.finrank ℝ E' ≤ m) (α : RoughForm IM M ℝ (r + m)) (v : Fin r → TangentSpace I b)
    {X : Fin r → (y : F) → TangentSpace IM (e.toOpenPartialHomeomorph.symm (b, y))}
    (hX : ∀ i y, mfderiv IM I proj (e.toOpenPartialHomeomorph.symm (b, y)) (X i y) = v i)
    (y : F) (w : Fin m → TangentSpace J y) :
    e.fiberIntegrand α b v y w = α (e.toOpenPartialHomeomorph.symm (b, y))
      (Fin.append (fun i ↦ X i y)
        fun j ↦ mfderiv J IM (fun y ↦ e.toOpenPartialHomeomorph.symm (b, y)) y (w j)) := by
  let D := mfderiv (I.prod J) IM e.toOpenPartialHomeomorph.symm (b, y)
  have hsymm : MDifferentiableAt (I.prod J) IM e.toOpenPartialHomeomorph.symm (b, y) :=
    he.mdifferentiableAt_symm (e.mem_target.2 hb)
  -- The derivative of the fibre inclusion is that of `e⁻¹` on vertical vectors.
  have hι (u : TangentSpace J y) :
      mfderiv J IM (fun y ↦ e.toOpenPartialHomeomorph.symm (b, y)) y u = D (0, u) :=
    (hsymm.mfderiv_uncurry_apply_zero_mk
      (f := fun b y ↦ e.toOpenPartialHomeomorph.symm (b, y)) u).symm
  -- The vertical space at `e⁻¹ (b, y)` has dimension at most `m`.
  let V : Submodule ℝ (TangentSpace IM (e.toOpenPartialHomeomorph.symm (b, y))) :=
    (mfderiv J IM (fun y ↦ e.toOpenPartialHomeomorph.symm (b, y)) y).range
  have hV : Module.finrank ℝ V ≤ m := (LinearMap.finrank_range_le _).trans hm
  have : Module.Finite ℝ V := LinearMap.finiteDimensional_range _
  have hw (j : Fin m) : D (0, w j) ∈ V := ⟨w j, hι _⟩
  have hVker : V = (mfderiv IM I proj (e.toOpenPartialHomeomorph.symm (b, y))).ker := by
    have h := range_mfderiv_fiberInclusionMap he hb y
    rw [e.coe_fiberInclusionMap hb] at h
    exact h
  have hu (i : Fin r) : X i y - D (v i, 0) ∈ V := by
    rw [hVker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hX]
    exact sub_eq_zero.2 (mfderiv_proj_mfderiv_symm_apply he hb y (v i, 0)).symm
  have hlhs : (fun p ↦ D ((Manifold.tangentSpaceProdEquiv (b, y)).symm
      (Fin.append (fun i ↦ (v i, 0)) (fun j ↦ (0, w j)) p))) =
      Fin.append (fun i ↦ D (v i, 0)) fun j ↦ D (0, w j) := by
    funext p
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) p <;>
      simp only [Fin.append_left, Fin.append_right] <;>
      exact congrArg D (Manifold.tangentSpaceProdEquiv_symm_apply _ _)
  have hX' : (fun i ↦ X i y) = (fun i ↦ D (v i, 0)) + fun i ↦ X i y - D (v i, 0) := by
    funext i
    simp
  rw [fiberIntegrand_apply, hlhs, hX', funext hι,
    ContinuousAlternatingMap.map_append_add_of_mem _ hV _ hu hw]

/-- **The integrand in degree `m`.** For `r = 0` and `e⁻¹` differentiable on its target, the
integrand over a point `b` of the base set is the pull-back of `α`, read in degree `m` through the
cast `0 + m = m`, along the fibre inclusion `y ↦ e⁻¹ (b, y)`. -/
theorem fiberIntegrand_degree_zero
    (he : MDifferentiableOn (I.prod J) IM e.toOpenPartialHomeomorph.symm e.target) {b : B}
    (hb : b ∈ e.baseSet) (α : RoughForm IM M ℝ (0 + m)) (v : Fin 0 → TangentSpace I b) :
    e.fiberIntegrand α b v = mpullback J IM (fun y ↦ e.toOpenPartialHomeomorph.symm (b, y))
      (LinearEquiv.cast (R := ℝ) (M := fun k ↦ RoughForm IM M ℝ k) (zero_add m) α) := by
  funext y
  ext w
  have hsymm : MDifferentiableAt (I.prod J) IM e.toOpenPartialHomeomorph.symm (b, y) :=
    (he _ (e.mem_target.2 hb)).mdifferentiableAt (e.open_target.mem_nhds (e.mem_target.2 hb))
  rw [fiberIntegrand_apply, mpullback_apply, RoughForm.cast_apply]
  congr 1
  funext p
  obtain ⟨j, rfl⟩ : ∃ j, p = Fin.natAdd 0 j := ⟨Fin.cast (zero_add m) p, Fin.ext (by simp)⟩
  rw [Fin.append_right, comp_apply,
    show Fin.cast (zero_add m) (Fin.natAdd 0 j) = j from Fin.ext (by simp),
    Manifold.tangentSpaceProdEquiv_symm_apply]
  exact hsymm.mfderiv_uncurry_apply_zero_mk (f := fun b y ↦ e.toOpenPartialHomeomorph.symm (b, y))
    (w j)

/-- **Changing the trivialization.** Let `e` be differentiable with differentiable inverse, let the
inverse of `e'` be differentiable on its target, let `b` lie in both base sets, and let the model
space of `F` have dimension at most `m`. The integrand read through `e'` is the pull-back of the
integrand read through `e` along the coordinate change `e'.coordChange e b` from `e'` to `e` over
`b`. -/
theorem fiberIntegrand_eq_mpullback_coordChange [FiniteDimensional ℝ E']
    {e e' : Trivialization F proj} (he : e.toOpenPartialHomeomorph.MDifferentiable IM (I.prod J))
    (he' : MDifferentiableOn (I.prod J) IM e'.toOpenPartialHomeomorph.symm e'.target) {b : B}
    (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) (hm : Module.finrank ℝ E' ≤ m)
    (α : RoughForm IM M ℝ (r + m)) (v : Fin r → TangentSpace I b) :
    e'.fiberIntegrand α b v = mpullback J J (e'.coordChange e b) (e.fiberIntegrand α b v) := by
  -- The coordinate change, extended to all of `B × F` so that it covers the identity of `B`.
  let Φ : B × F → B × F := fun p ↦ (p.1, e'.coordChange e p.1 p.2)
  have hd (y : F) : MDifferentiableAt (I.prod J) (I.prod J) Φ (b, y) := by
    have hy : ((b, y) : B × F) ∈ e'.target := e'.mem_target.2 hb'
    have hs : e'.toOpenPartialHomeomorph.symm (b, y) ∈ e.source :=
      e.mem_source.2 (by rwa [e'.proj_symm_apply' hb'])
    -- By definition, `e'.coordChange e p.1 p.2` is `(e (e'⁻¹ p)).2`.
    exact mdifferentiableAt_fst.prodMk ((he.mdifferentiableAt hs).comp _
      ((he' _ hy).mdifferentiableAt (e'.open_target.mem_nhds hy))).snd
  -- Over both base sets, `e⁻¹ ∘ Φ` is `e'⁻¹`.
  have hev (y : F) : (e.toOpenPartialHomeomorph.symm ∘ Φ) =ᶠ[nhds (b, y)]
      e'.toOpenPartialHomeomorph.symm := by
    filter_upwards [((e.open_baseSet.inter e'.open_baseSet).preimage continuous_fst).mem_nhds
      ⟨hb, hb'⟩] with p hp
    simpa [fiberInclusionMap_apply] using e'.fiberInclusionMap_coordChange e hp.2 hp.1 p.2
  funext y
  rw [fiberIntegrand_def, fiberIntegrand_def,
    ← prodFiberIntegrand_mpullback_of_fst_eq (Φ := Φ) rfl hd hm]
  ext w
  rw [prodFiberIntegrand_apply, prodFiberIntegrand_apply, ← mpullback_comp_at (hd y)
    (he.mdifferentiableAt_symm (e.mem_target.2 hb)),
    mpullback_apply_eq_of_mfderiv_eq (hev y).eq_of_nhds (hev y).mfderiv_eq]

end Bundle.Trivialization

namespace TauCeti.MapFiber.Atlas

open SymplecticGeometry TauCeti

variable (A : Atlas F proj)

/-- **The integrand of the fibre integral of a fibration with an atlas.** For a form `α` of
degree `r + m` on `M`, a point `b : B` and tangent vectors `v₁, …, vᵣ` at `b`, the integrand over
`b` read through the chart `A.trivAt b` of the atlas at `b`. -/
def fiberIntegrand (α : RoughForm IM M ℝ (r + m)) (b : B) (v : Fin r → TangentSpace I b) :
    RoughForm J F ℝ m :=
  (A.trivAt b).fiberIntegrand α b v

theorem fiberIntegrand_def (α : RoughForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) :
    A.fiberIntegrand (J := J) α b v = (A.trivAt b).fiberIntegrand α b v :=
  (rfl)

/-- The value of the integrand at `y` on `w` is that of `α` at `e⁻¹ (b, y)` on the images of
`(v₁, 0), …, (vᵣ, 0), (0, w₁), …, (0, wₘ)` under the derivative of `e⁻¹` at `(b, y)`, for the
chart `e = A.trivAt b`. -/
@[simp]
theorem fiberIntegrand_apply (α : RoughForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) (y : F) (w : Fin m → TangentSpace J y) :
    A.fiberIntegrand α b v y w = α ((A.trivAt b).toOpenPartialHomeomorph.symm (b, y)) (fun p ↦
      mfderiv (I.prod J) IM (A.trivAt b).toOpenPartialHomeomorph.symm (b, y)
        ((Manifold.tangentSpaceProdEquiv (b, y)).symm
          (Fin.append (fun i ↦ (v i, 0)) (fun j ↦ (0, w j)) p))) := by
  rw [fiberIntegrand_def, Bundle.Trivialization.fiberIntegrand_apply]

/-- The integrand is additive in the form. -/
@[simp]
theorem fiberIntegrand_add (α β : RoughForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) :
    A.fiberIntegrand (J := J) (α + β) b v = A.fiberIntegrand α b v + A.fiberIntegrand β b v := by
  simp only [fiberIntegrand_def, Bundle.Trivialization.fiberIntegrand_add]

/-- The integrand is homogeneous in the form. -/
@[simp]
theorem fiberIntegrand_smul (c : ℝ) (α : RoughForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) :
    A.fiberIntegrand (J := J) (c • α) b v = c • A.fiberIntegrand α b v := by
  simp only [fiberIntegrand_def, Bundle.Trivialization.fiberIntegrand_smul]

/-- The integrand of the zero form is zero. -/
@[simp]
theorem fiberIntegrand_zero (b : B) (v : Fin r → TangentSpace I b) :
    A.fiberIntegrand (J := J) (0 : RoughForm IM M ℝ (r + m)) b v = 0 := by
  simp only [fiberIntegrand_def, Bundle.Trivialization.fiberIntegrand_zero]

/-- The integrand of `-α` is minus that of `α`. -/
@[simp]
theorem fiberIntegrand_neg (α : RoughForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) :
    A.fiberIntegrand (J := J) (-α) b v = -A.fiberIntegrand α b v := by
  simp only [fiberIntegrand_def, Bundle.Trivialization.fiberIntegrand_neg]

/-- The integrand is subtractive in the form. -/
@[simp]
theorem fiberIntegrand_sub (α β : RoughForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) :
    A.fiberIntegrand (J := J) (α - β) b v = A.fiberIntegrand α b v - A.fiberIntegrand β b v := by
  simp only [fiberIntegrand_def, Bundle.Trivialization.fiberIntegrand_sub]

/-- The integrand is additive in each base vector `v i`. -/
theorem fiberIntegrand_update_add [DecidableEq (Fin r)] (α : RoughForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) (i : Fin r) (x x' : TangentSpace I b) :
    A.fiberIntegrand (J := J) α b (update v i (x + x')) =
      A.fiberIntegrand α b (update v i x) + A.fiberIntegrand α b (update v i x') :=
  (A.trivAt b).fiberIntegrand_update_add α b v i x x'

/-- The integrand is homogeneous in each base vector `v i`. -/
theorem fiberIntegrand_update_smul [DecidableEq (Fin r)] (α : RoughForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) (i : Fin r) (c : ℝ) (x : TangentSpace I b) :
    A.fiberIntegrand (J := J) α b (update v i (c • x)) =
      c • A.fiberIntegrand α b (update v i x) :=
  (A.trivAt b).fiberIntegrand_update_smul α b v i c x

/-- The integrand vanishes when two base vectors are equal. -/
theorem fiberIntegrand_eq_zero_of_eq (α : RoughForm IM M ℝ (r + m)) (b : B)
    {v : Fin r → TangentSpace I b} {i j : Fin r} (hv : v i = v j) (hij : i ≠ j) :
    A.fiberIntegrand (J := J) α b v = 0 :=
  (A.trivAt b).fiberIntegrand_eq_zero_of_eq α b hv hij

variable {A} {n : ℕ∞ω}

/-- **The integrand as that of a product.** For a `C^n` atlas, `n ≠ 0`, let `U` be the base set of
the chart `e = A.trivAt b`, as an open set of `B`. The integrand over `b` is the integrand over
`⟨b, _⟩` of the pull-back of `α` to `U × F` along `(b', y) ↦ e⁻¹ (b', y)`. -/
theorem fiberIntegrand_eq_prodFiberIntegrand (hA : A.IsContMDiff n I J IM) (hn : n ≠ 0)
    (α : RoughForm IM M ℝ (r + m)) (b : B) (v : Fin r → TangentSpace I b) :
    A.fiberIntegrand α b v = prodFiberIntegrand
      (mpullback (I.prod J) IM (fun p : (⟨(A.trivAt b).baseSet, (A.trivAt b).open_baseSet⟩ :
        TopologicalSpace.Opens B) × F ↦ (A.trivAt b).toOpenPartialHomeomorph.symm (p.1, p.2)) α)
      ⟨b, A.mem_baseSet_trivAt b⟩ v :=
  (A.trivAt b).fiberIntegrand_eq_prodFiberIntegrand
    ((hA.contMDiffOn_trivAt_symm b).mdifferentiableOn hn) subset_rfl α ⟨b, A.mem_baseSet_trivAt b⟩ v

/-- **The integrand does not depend on the lifts.** For a `C^n` atlas, `n ≠ 0`, whose model fibre
has a model space of dimension at most `m`, let `e = A.trivAt b` be the chart at `b`, and let
`Xᵢ y` be tangent vectors of `M` at `e⁻¹ (b, y)` that the derivative of `proj` sends to `vᵢ`. The
integrand at `y` sends `w` to the value of `α` at `e⁻¹ (b, y)` on `X₁ y, …, Xᵣ y` followed by the
images of `w₁, …, wₘ` under the derivative of the fibre inclusion `y ↦ e⁻¹ (b, y)`. -/
theorem fiberIntegrand_apply_of_lift [FiniteDimensional ℝ E'] (hA : A.IsContMDiff n I J IM)
    (hn : n ≠ 0) (hm : Module.finrank ℝ E' ≤ m) (α : RoughForm IM M ℝ (r + m)) {b : B}
    (v : Fin r → TangentSpace I b)
    {X : Fin r → (y : F) → TangentSpace IM ((A.trivAt b).toOpenPartialHomeomorph.symm (b, y))}
    (hX : ∀ i y,
      mfderiv IM I proj ((A.trivAt b).toOpenPartialHomeomorph.symm (b, y)) (X i y) = v i)
    (y : F) (w : Fin m → TangentSpace J y) :
    A.fiberIntegrand α b v y w = α ((A.trivAt b).toOpenPartialHomeomorph.symm (b, y))
      (Fin.append (fun i ↦ X i y)
        fun j ↦ mfderiv J IM (fun y ↦ (A.trivAt b).toOpenPartialHomeomorph.symm (b, y)) y (w j))
    := by
  rw [fiberIntegrand_def]
  exact (A.trivAt b).fiberIntegrand_apply_of_lift (hA.mdifferentiable_trivAt hn b)
    (A.mem_baseSet_trivAt b) hm α v hX y w

/-- **The integrand in degree `m`.** For a `C^n` atlas, `n ≠ 0`, and `r = 0`, the integrand over
`b` is the pull-back of `α`, read in degree `m` through the cast `0 + m = m`, along the fibre
inclusion `y ↦ e⁻¹ (b, y)` of the chart `e = A.trivAt b`. -/
theorem fiberIntegrand_degree_zero (hA : A.IsContMDiff n I J IM) (hn : n ≠ 0)
    (α : RoughForm IM M ℝ (0 + m)) (b : B) (v : Fin 0 → TangentSpace I b) :
    A.fiberIntegrand α b v =
      mpullback J IM (fun y ↦ (A.trivAt b).toOpenPartialHomeomorph.symm (b, y))
        (LinearEquiv.cast (R := ℝ) (M := fun k ↦ RoughForm IM M ℝ k) (zero_add m) α) :=
  (A.trivAt b).fiberIntegrand_degree_zero ((hA.contMDiffOn_trivAt_symm b).mdifferentiableOn hn)
    (A.mem_baseSet_trivAt b) α v

/-- **The integral of the integrand does not depend on the chart.** Let `A` be a `C^n` atlas,
`n ≠ 0`, whose coordinate changes preserve the orientation `o` of `F`. For every chart
`A.trivAt b'` whose base set contains `b`, the integral over `F` of the integrand read through
`A.trivAt b'` is that of the integrand read through the chart `A.trivAt b` at `b`. -/
theorem integralTopForm_fiberIntegrand_trivAt [FiniteDimensional ℝ E'] [IsManifold J 1 F]
    (o : Manifold.Orientation J F (Fin m)) (hA : A.IsContMDiff n I J IM) {hn : n ≠ 0}
    (ho : A.HasStructureGroup (Diffeomorph.orientationPreservingSubgroup hn o))
    (α : RoughForm IM M ℝ (r + m)) {b b' : B} (hb : b ∈ (A.trivAt b').baseSet)
    (v : Fin r → TangentSpace I b) :
    integralTopForm o ((A.trivAt b').fiberIntegrand α b v) =
      integralTopForm o (A.fiberIntegrand α b v) := by
  obtain ⟨φ, hφ, hφe⟩ := hasStructureGroup_iff.1 ho b' b b hb (A.mem_baseSet_trivAt b)
  rw [fiberIntegrand_def, Trivialization.fiberIntegrand_eq_mpullback_coordChange
    (hA.mdifferentiable_trivAt hn b) ((hA.contMDiffOn_trivAt_symm b').mdifferentiableOn hn)
    (A.mem_baseSet_trivAt b) hb (by simpa using o.card_eq.symm.le) α v, ← hφe]
  exact φ.toHomeomorph.isOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt
    (Diffeomorph.mem_orientationPreservingSubgroup_iff.mp hφ) (by simp)

section Operator

variable [IsManifold I ∞ B] [IsManifold J ∞ F] [IsManifold IM 1 M]

/-- **The integrand of a smooth form is smooth.** For a smooth atlas, the integrand over `b` of a
smooth form on `M` is a smooth form on `F`. -/
theorem isSmoothForm_fiberIntegrand (hA : A.IsContMDiff ∞ I J IM)
    (α : SmoothForm IM M ℝ (r + m)) (b : B) (v : Fin r → TangentSpace I b) :
    IsSmoothForm J ∞ (A.fiberIntegrand α.val b v) := by
  have h := (SmoothForm.mpullback _ ((A.trivAt b).contMDiff_symm_val_prod
    (hA.contMDiffOn_trivAt_symm b) (U := ⟨(A.trivAt b).baseSet, (A.trivAt b).open_baseSet⟩)
    subset_rfl) α).isSmoothForm
  rw [SmoothForm.coe_mpullback] at h
  rw [fiberIntegrand_eq_prodFiberIntegrand hA (by simp)]
  exact isSmoothForm_prodFiberIntegrand h _ v

variable [FiniteDimensional ℝ E'] [CompactSpace F]

variable (o : Manifold.Orientation J F (Fin m))

/-- For a smooth atlas and a smooth form `α`, the alternating map `v ↦ ∫_F A.fiberIntegrand α b v`
of the base vectors at `b`. -/
private def fiberIntegralAlternatingMap (hA : A.IsContMDiff ∞ I J IM)
    (α : SmoothForm IM M ℝ (r + m)) (b : B) : TangentSpace I b [⋀^Fin r]→ₗ[ℝ] ℝ where
  toFun v := integralTopForm o (A.fiberIntegrand α.val b v)
  map_update_add' v i x x' := by
    rw [fiberIntegrand_update_add, integralTopForm_add_of_compactSpace o
      ((isSmoothForm_fiberIntegrand hA α b _).of_le bot_le)
      ((isSmoothForm_fiberIntegrand hA α b _).of_le bot_le)]
  map_update_smul' v i c x := by
    rw [fiberIntegrand_update_smul, integralTopForm_smul, smul_eq_mul, RingHom.id_apply]
  map_eq_zero_of_eq' v i j hv hij := by
    rw [fiberIntegrand_eq_zero_of_eq A α.val b hv hij, integralTopForm_zero]

private theorem fiberIntegralAlternatingMap_apply (hA : A.IsContMDiff ∞ I J IM)
    (α : SmoothForm IM M ℝ (r + m)) (b : B) (v : Fin r → TangentSpace I b) :
    fiberIntegralAlternatingMap o hA α b v = integralTopForm o (A.fiberIntegrand α.val b v) :=
  (rfl)

variable [FiniteDimensional ℝ E]

/-- The rough form underlying the fibre integral: at `b`, the continuous alternating map
`v ↦ ∫_F A.fiberIntegrand α b v`. -/
private def fiberIntegralRoughForm (hA : A.IsContMDiff ∞ I J IM)
    (α : SmoothForm IM M ℝ (r + m)) : RoughForm I B ℝ r := fun b ↦
  AlternatingMap.toContinuousAlternatingMap (fiberIntegralAlternatingMap o hA α b)

private theorem fiberIntegralRoughForm_apply (hA : A.IsContMDiff ∞ I J IM)
    (α : SmoothForm IM M ℝ (r + m)) (b : B) (v : Fin r → TangentSpace I b) :
    fiberIntegralRoughForm o hA α b v = integralTopForm o (A.fiberIntegrand α.val b v) := by
  rw [fiberIntegralRoughForm, AlternatingMap.coe_toContinuousAlternatingMap,
    fiberIntegralAlternatingMap_apply]

variable [BoundarylessManifold I B] [T2Space F]

/-- On the base set `U` of a chart, the restriction of the fibre integral is the fibre integral
on the product `U × F` of the pull-back along `(b, y) ↦ e⁻¹ (b, y)`. -/
private theorem mpullback_subtype_val_fiberIntegralRoughForm (hA : A.IsContMDiff ∞ I J IM)
    {hn : (∞ : ℕ∞ω) ≠ 0} (ho : A.HasStructureGroup (Diffeomorph.orientationPreservingSubgroup hn o))
    (α : SmoothForm IM M ℝ (r + m)) (b' : B) :
    mpullback I I (Subtype.val : (⟨(A.trivAt b').baseSet, (A.trivAt b').open_baseSet⟩ :
        TopologicalSpace.Opens B) → B) (fiberIntegralRoughForm o hA α) =
      (prodFiberIntegral o (SmoothForm.mpullback _ ((A.trivAt b').contMDiff_symm_val_prod
        (hA.contMDiffOn_trivAt_symm b') subset_rfl) α)).val := by
  funext b
  ext v
  rw [mpullback_subtype_val_apply, prodFiberIntegral_apply, SmoothForm.coe_mpullback]
  refine (fiberIntegralRoughForm_apply o hA α b v).trans ?_
  refine (integralTopForm_fiberIntegrand_trivAt o hA ho α.val b.property v).symm.trans ?_
  rw [(A.trivAt b').fiberIntegrand_eq_prodFiberIntegrand
    ((hA.contMDiffOn_trivAt_symm b').mdifferentiableOn (by simp)) subset_rfl]

private theorem isSmoothForm_fiberIntegralRoughForm (hA : A.IsContMDiff ∞ I J IM)
    {hn : (∞ : ℕ∞ω) ≠ 0} (ho : A.HasStructureGroup (Diffeomorph.orientationPreservingSubgroup hn o))
    (α : SmoothForm IM M ℝ (r + m)) : IsSmoothForm I ∞ (fiberIntegralRoughForm o hA α) := by
  refine (isSmoothForm_def _ _).2 fun b ↦ ?_
  have h := (prodFiberIntegral o (SmoothForm.mpullback _ ((A.trivAt b).contMDiff_symm_val_prod
    (hA.contMDiffOn_trivAt_symm b) (U := ⟨(A.trivAt b).baseSet, (A.trivAt b).open_baseSet⟩)
    subset_rfl) α)).isSmoothForm
  rw [← mpullback_subtype_val_fiberIntegralRoughForm o hA ho α b, isSmoothForm_def] at h
  exact (contMDiffAt_mpullback_subtype_val_iff _ ⟨b, A.mem_baseSet_trivAt b⟩).1 (h _)

variable {o} in
/-- **The fibre integral of a fibration with an oriented atlas.** Let `A` be a smooth atlas of
`proj : M → B` whose coordinate changes preserve the orientation `o` of the compact Hausdorff
model fibre `F`, and let `B` be boundaryless. The linear map sending a smooth form `α` of degree
`r + m` on `M` to the smooth `r`-form on `B` whose value at `b` on `v₁, …, vᵣ` is the integral
over `F` of the integrand `A.fiberIntegrand α b v`. -/
def fiberIntegral (hA : A.IsContMDiff ∞ I J IM) {hn : (∞ : ℕ∞ω) ≠ 0}
    (ho : A.HasStructureGroup (Diffeomorph.orientationPreservingSubgroup hn o)) :
    SmoothForm IM M ℝ (r + m) →ₗ[ℝ] SmoothForm I B ℝ r where
  toFun α := ⟨fiberIntegralRoughForm o hA α,
    (isSmoothForm_fiberIntegralRoughForm o hA ho α).mem_smoothBundleForms⟩
  map_add' α β := SmoothBundleForm.ext fun b v ↦ by
    simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
      fiberIntegralRoughForm_apply, fiberIntegrand_add]
    exact integralTopForm_add_of_compactSpace o
      ((isSmoothForm_fiberIntegrand hA α b v).of_le bot_le)
      ((isSmoothForm_fiberIntegrand hA β b v).of_le bot_le)
  map_smul' c α := SmoothBundleForm.ext fun b v ↦ by
    simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
      fiberIntegralRoughForm_apply, fiberIntegrand_smul, integralTopForm_smul,
      RingHom.id_apply, smul_eq_mul]

variable (hA : A.IsContMDiff ∞ I J IM) {hn : (∞ : ℕ∞ω) ≠ 0}
  (ho : A.HasStructureGroup (Diffeomorph.orientationPreservingSubgroup hn o))

/-- The value of the fibre integral at `b` on `v` is the integral over `F` of the integrand read
through the chart `A.trivAt b`. -/
@[simp]
theorem fiberIntegral_apply (α : SmoothForm IM M ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) :
    (A.fiberIntegral hA ho α).val b v = integralTopForm o (A.fiberIntegrand α.val b v) :=
  fiberIntegralRoughForm_apply o hA α b v

/-- **The value in a trivialization.** On the base set `U` of the chart `e = A.trivAt b'`, the
restriction of the fibre integral of `α` is the fibre integral on the product `U × F` of the
pull-back of `α` along `(b, y) ↦ e⁻¹ (b, y)`. -/
theorem mpullback_subtype_val_fiberIntegral (α : SmoothForm IM M ℝ (r + m)) (b' : B) :
    SmoothForm.mpullback (Subtype.val : (⟨(A.trivAt b').baseSet, (A.trivAt b').open_baseSet⟩ :
        TopologicalSpace.Opens B) → B) contMDiff_subtypeVal (A.fiberIntegral hA ho α) =
      prodFiberIntegral o (SmoothForm.mpullback _ ((A.trivAt b').contMDiff_symm_val_prod
        (hA.contMDiffOn_trivAt_symm b') subset_rfl) α) :=
  SmoothBundleForm.ext fun b v ↦ by
    rw [SmoothForm.coe_mpullback, ← mpullback_subtype_val_fiberIntegralRoughForm o hA ho α b',
      mpullback_subtype_val_apply, mpullback_subtype_val_apply]
    exact (fiberIntegral_apply o hA ho α b v).trans (fiberIntegralRoughForm_apply o hA α b v).symm

/-- **The fibre integral does not depend on the chart.** For every chart `A.trivAt b'` whose
base set contains `b`, the value of the fibre integral at `b` on `v` is the integral over `F` of
the integrand read through `A.trivAt b'`. -/
theorem fiberIntegral_apply_of_mem (α : SmoothForm IM M ℝ (r + m)) {b b' : B}
    (hb : b ∈ (A.trivAt b').baseSet) (v : Fin r → TangentSpace I b) :
    (A.fiberIntegral hA ho α).val b v =
      integralTopForm o ((A.trivAt b').fiberIntegrand α.val b v) := by
  rw [fiberIntegral_apply, integralTopForm_fiberIntegrand_trivAt o hA ho α.val hb]

/-- **The fibre integral through any lifts.** Let `e = A.trivAt b'` be a chart whose base set
contains `b`, and let `Xᵢ y` be tangent vectors of `M` at `e⁻¹ (b, y)` that the derivative of
`proj` sends to `vᵢ`. The value of the fibre integral at `b` on `v` is the integral over `F` of
the pull-back along the fibre inclusion `y ↦ e⁻¹ (b, y)` of `α` with its first `r` arguments
set to `X₁ y, …, Xᵣ y`. No regularity in `y` is asked of the `Xᵢ`. -/
theorem fiberIntegral_apply_of_lift (α : SmoothForm IM M ℝ (r + m)) {b b' : B}
    (hb : b ∈ (A.trivAt b').baseSet) (v : Fin r → TangentSpace I b)
    {X : Fin r → (y : F) → TangentSpace IM ((A.trivAt b').toOpenPartialHomeomorph.symm (b, y))}
    (hX : ∀ i y,
      mfderiv IM I proj ((A.trivAt b').toOpenPartialHomeomorph.symm (b, y)) (X i y) = v i) :
    (A.fiberIntegral hA ho α).val b v = integralTopForm o (fun y ↦
      ((α.val ((A.trivAt b').toOpenPartialHomeomorph.symm (b, y))).appendLeft
        fun i ↦ X i y).compContinuousLinearMap
          (mfderiv J IM (fun y ↦ (A.trivAt b').toOpenPartialHomeomorph.symm (b, y)) y)) := by
  rw [fiberIntegral_apply_of_mem o hA ho α hb]
  congr 1
  funext y
  ext w
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.appendLeft_apply]
  exact (A.trivAt b').fiberIntegrand_apply_of_lift (hA.mdifferentiable_trivAt (by simp) b') hb
    (by simpa using o.card_eq.symm.le) α.val v hX y w

/-- **The integral over each fibre.** In degree `m` (`r = 0`), the value of the fibre integral at
`b` is the integral over `F` of the pull-back of `α`, read in degree `m` through the cast
`0 + m = m`, along the fibre inclusion `y ↦ e⁻¹ (b, y)`, for every chart `e = A.trivAt b'` whose
base set contains `b`. -/
theorem fiberIntegral_apply_zero (α : SmoothForm IM M ℝ (0 + m)) {b b' : B}
    (hb : b ∈ (A.trivAt b').baseSet) (v : Fin 0 → TangentSpace I b) :
    (A.fiberIntegral hA ho α).val b v = integralTopForm o
      (mpullback J IM (fun y ↦ (A.trivAt b').toOpenPartialHomeomorph.symm (b, y))
        (LinearEquiv.cast (R := ℝ) (M := fun k ↦ SmoothForm IM M ℝ k) (zero_add m) α).val) := by
  rw [fiberIntegral_apply_of_mem o hA ho α hb, (A.trivAt b').fiberIntegrand_degree_zero
    ((hA.contMDiffOn_trivAt_symm b').mdifferentiableOn (by simp)) hb]
  congr 2
  funext x
  ext w
  rw [RoughForm.cast_apply, SmoothForm.cast_apply]

end Operator

end TauCeti.MapFiber.Atlas

end
