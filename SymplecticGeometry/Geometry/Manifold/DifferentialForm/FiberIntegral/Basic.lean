/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.Basic
public import TauCeti.Geometry.Manifold.FiberBundle.MapFiber
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.Naturality
import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The integrand of the fibre integral of a fibration with an atlas

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

## Main definitions

* `Bundle.Trivialization.fiberIntegrand e α b v`: the integrand read through `e`.
* `TauCeti.MapFiber.Atlas.fiberIntegrand A α b v`: the integrand read through `A.trivAt b`.

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
has a model space of dimension at most `m`, let `e = A.trivAt b'` be a chart with `b` in its base
set, and let `Xᵢ y` be tangent vectors of `M` at `e⁻¹ (b, y)` that the derivative of `proj` sends
to `vᵢ`. The integrand read through `e` sends `w` at `y` to the value of `α` at `e⁻¹ (b, y)` on
`X₁ y, …, Xᵣ y` followed by the images of `w₁, …, wₘ` under the derivative of the fibre inclusion
`y ↦ e⁻¹ (b, y)`. -/
theorem fiberIntegrand_apply_of_lift [FiniteDimensional ℝ E'] (hA : A.IsContMDiff n I J IM)
    (hn : n ≠ 0) (hm : Module.finrank ℝ E' ≤ m) {b' b : B} (hb : b ∈ (A.trivAt b').baseSet)
    (α : RoughForm IM M ℝ (r + m)) (v : Fin r → TangentSpace I b)
    {X : Fin r → (y : F) → TangentSpace IM ((A.trivAt b').toOpenPartialHomeomorph.symm (b, y))}
    (hX : ∀ i y,
      mfderiv IM I proj ((A.trivAt b').toOpenPartialHomeomorph.symm (b, y)) (X i y) = v i)
    (y : F) (w : Fin m → TangentSpace J y) :
    (A.trivAt b').fiberIntegrand α b v y w = α ((A.trivAt b').toOpenPartialHomeomorph.symm (b, y))
      (Fin.append (fun i ↦ X i y)
        fun j ↦ mfderiv J IM (fun y ↦ (A.trivAt b').toOpenPartialHomeomorph.symm (b, y)) y (w j)) :=
  (A.trivAt b').fiberIntegrand_apply_of_lift (hA.mdifferentiable_trivAt hn b') hb hm α v hX y w

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

end TauCeti.MapFiber.Atlas

end
