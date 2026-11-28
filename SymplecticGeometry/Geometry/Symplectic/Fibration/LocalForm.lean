/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.CoordOneForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Vertical
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
public import TauCeti.Geometry.Manifold.VectorField.Prod
public import SymplecticGeometry.Geometry.Symplectic.Fibration.HorizontalDistribution
public import TauCeti.Geometry.Symplectic.Manifold.Flat
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Interior
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Symplectic.Manifold.Family
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Geometry.Manifold.VectorField.Prod
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.MixedPartial
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.VectorField.ModelChart

/-!
# The local form of a two-form on a product

Let `τ` be a two-form on `EB × F`, where `EB` is a real normed space, `F` a manifold modelled by
`IF`, and `EB × F` is modelled by `𝓘(ℝ, EB).prod IF`. Such a form arises as the reading of a
two-form on the total space of a fibration in a trivialization over a chart of the base. A basis
`bs` of `EB` gives coordinates `xᵢ = bs.coord i` and constant fields `∂ᵢ = bs i`. This file
splits `τ` into its components, each a family of objects on `F` indexed by the points `x` of `EB`:

* the slices `σ(x) = ι_x^* τ`, the two-forms on `F` obtained by pulling `τ` back along
  `ι_x = Prod.mk x` (`TauCeti.RoughForm.fiberComponent`);
* the one-forms `αᵢ(x) = -ι_x^* (ι(∂ᵢ, 0) τ)` on `F` (`TauCeti.RoughForm.mixedComponent`);
* the functions `f_{ij}(x) = τ((∂ᵢ, 0), (∂ⱼ, 0))` on `F` (`TauCeti.RoughForm.baseComponent`).

The families of forms become forms on `EB × F` through Tau Ceti's `TauCeti.verticalForm`, and
then `τ = σ + ∑ᵢ αᵢ ∧ dxᵢ + ∑_{i<j} f_{ij} dxᵢ ∧ dxⱼ`
(`TauCeti.RoughForm.eq_verticalForm_add_sum`), where `dxᵢ` is the constant one-form
`Module.Basis.coordOneForm bs i` on `EB` pulled back along `Prod.fst`. The sign of `αᵢ` is the one
for which this formula holds: `αᵢ(x)` evaluates `τ` on a vector `(0, w)` followed by `(∂ᵢ, 0)`.
The identity holds at every point, since it is a statement about the values of `τ` at each point
of `EB × F`; no regularity of `τ` is needed.

The exterior derivative of `τ` is then read in terms of the components. If `τ` is `C¹` at
`(x, y)`, then on two vectors `w₁, w₂` tangent to the fibre and the field `∂ᵢ`,

`dτ((0, w₁), (0, w₂), (∂ᵢ, 0)) = ∂ᵢσ(x)(w₁, w₂) + d_F αᵢ(x)(w₁, w₂)`

(`TauCeti.RoughForm.mextDeriv_apply_eq_fderivFiberComponent_add_mextDeriv_mixedComponent`), where
`∂ᵢσ(x)` is the derivative at `x` along `∂ᵢ` of the slices `x' ↦ σ(x')`, a two-form on `F`
(`TauCeti.RoughForm.fderivFiberComponent`), and `d_F` is the exterior derivative of `F`. This is
one of the equations (6.3.5)–(6.3.7) of [McDuffSalamon2017], with the sign of `αᵢ` fixed above.
Splitting a third vector `(a, u)` as `(0, u) + ∑ᵢ xᵢ(a) (∂ᵢ, 0)`, it follows that `τ` is
vertically closed for the first projection at the points over `x` exactly when `σ(x)` is closed
and `∂ᵢσ(x) + d_F αᵢ(x) = 0` for every `i` (`TauCeti.RoughForm.isVerticallyClosed_iff_local`).

For a smooth two-form `τ` whose fibre components are all nondegenerate, the first projection
carries the connection `TauCeti.SmoothTwoForm.horizontalDistribution` of `τ`. The flat maps of
`σ(x)` are then invertible, which gives vector fields `Xᵢ(x)` on `F` with
`ι(Xᵢ(x)) σ(x) = αᵢ(x)`, and `Xᵢ(x)(y)` is the only tangent vector with this property
(`TauCeti.SmoothTwoForm.mixedVectorField_eq_iff`). The horizontal lift of `∂ᵢ` at `(x, y)` is
`(∂ᵢ, Xᵢ(x)(y))` (`TauCeti.SmoothTwoForm.horizontalLift_local`), and `Xᵢ` is smooth in `(x, y)`,
since it inverts the flat maps of the smooth family `σ`.

## Main definitions

* `TauCeti.RoughForm.fiberComponent τ x`: the slice of `τ` over `x`.
* `TauCeti.RoughForm.mixedComponent τ bs i x`: the one-form `αᵢ(x)` on `F`.
* `TauCeti.RoughForm.mixedCurl τ bs i j x y w`: the value at `w ∈ T_y F` of the one-form
  `∂ᵢαⱼ(x) - ∂ⱼαᵢ(x)` on `F`.
* `TauCeti.RoughForm.baseComponent τ bs i j x`: the function `f_{ij}(x)` on `F`.
* `TauCeti.RoughForm.fderivFiberComponent τ x v`: the derivative `∂_v σ(x)` of the slices along
  `v ∈ EB`, a two-form on `F`.
* `TauCeti.SmoothTwoForm.smoothFiberComponent τ x`: the slice of a smooth `τ`, as a smooth form.
* `TauCeti.SmoothTwoForm.mixedVectorField τ bs i x`: the vector field `Xᵢ(x)` on `F`, the inverse
  of the flat map of `σ(x)` applied to `αᵢ(x)`.
* `SymplecticGeometry.baseField bs i`: the constant field `(∂ᵢ, 0)` on `EB × F`, as a smooth
  section.

## Main results

* `TauCeti.RoughForm.eq_verticalForm_add_sum`: the local form of `τ`.
* `TauCeti.RoughForm.fiberComponent_add`, `fiberComponent_fun_smul` and their neighbours: the
  slice over `x` is linear in `τ`, and a factor `g` on `EB × F` restricts to the fibre as
  `y ↦ g (x, y)`; by `fiberComponent_fun_smul_fst`, a factor `f(x)` that depends only on the base
  point comes out of the slice over `x` as the scalar `f x`.
* `TauCeti.RoughForm.mextDeriv_fiberComponent_apply`: on vectors tangent to the fibre over `x`,
  the exterior derivative of `τ` is that of its slice `σ(x)`, for `τ` of class `C¹` at the point.
* `TauCeti.RoughForm.differentiableAt_fiberComponent`: the slices of a form differentiable at
  `(x, y)` are differentiable in `x`.
* `TauCeti.RoughForm.contMDiffAt_mixedComponent`: the mixed components of a `C^n` form are `C^n`.
* `TauCeti.RoughForm.mextDeriv_apply_eq_fderivFiberComponent_add_mextDeriv_mixedComponent`: `dτ` on
  two fibre vectors and a base field.
* `TauCeti.RoughForm.mextDeriv_apply_eq_mextDeriv_fiberComponent_add_sum`: `dτ` on two fibre
  vectors and an arbitrary third vector, through `d(σ(x))`, `∂ᵢσ(x)` and `d_F αᵢ(x)`.
* `TauCeti.RoughForm.isVerticallyClosed_iff_local`: a `C¹` form on `U ×ˢ univ` is vertically closed
  there for the first projection exactly when each slice `σ(x)` is closed and
  `∂ᵢσ(x) + d_F αᵢ(x) = 0` for every `i`.
* `TauCeti.RoughForm.isVerticallyClosedOn_singleton_iff_local`: the same at a single point.
* `TauCeti.SmoothTwoForm.isVerticallyNondegenerate_fst_iff`: `τ` is vertically nondegenerate for
  the first projection exactly when every `σ(x)` is nondegenerate.
* `TauCeti.SmoothTwoForm.horizontalLift_local`: the horizontal lift of `∂ᵢ` is `(∂ᵢ, Xᵢ)`.
* `TauCeti.SmoothTwoForm.contMDiff_mixedVectorField`: `Xᵢ` is smooth jointly in `x` and the
  point of `F`.
* `TauCeti.SmoothTwoForm.contMDiff_mixedVectorField_of_isNondegenerate`: where `σ(x)` is
  nondegenerate, `Xᵢ(x)` is a smooth vector field on `F`.
* `TauCeti.SmoothTwoForm.contMDiff_eval₂_mixedVectorField`: where `σ(x)` is nondegenerate, the
  function `σ(x)(Xᵢ(x), Xⱼ(x))` on `F` is smooth.
* `TauCeti.SmoothTwoForm.contMDiff_baseComponent`: the base components `f_{ij}` of a smooth `τ`
  are smooth jointly in `x` and the point of `F`.
* `TauCeti.SmoothTwoForm.fderiv_mixedComponent_sub_fderiv_mixedComponent`: the curl
  `∂ᵢαⱼ(x) - ∂ⱼαᵢ(x)` of the mixed components, on a vector `w` tangent to `F`, is
  `d_F f_{ij}(x)(w) - dτ((∂ᵢ, 0), (∂ⱼ, 0), (0, w))`.

## Implementation notes

By Tau Ceti's `TauCeti.mpullback_prodMk_verticalForm`, the slices over `x` of the vertical forms
of `σ` and `αᵢ` are `σ(x)` and `αᵢ(x)`, so the components can be recovered from the terms of the
local form. The proof of the local form is linear algebra at each point: it applies
`ContinuousAlternatingMap.apply_vecCons_prod_eq_sum`, the same splitting for a single
continuous alternating two-form on a product, to the value of `τ` at that point.

The smoothness of `Xᵢ` comes from inverting `σ(x)`. The vector field `Xᵢ(x)` is the image under
the inverse of `TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv` of `σ(x)` of the slice over
`x` of the smooth one-form `-ι(∂ᵢ, 0) τ`
(`TauCeti.SmoothTwoForm.mixedVectorField_eq_interiorEquiv_symm`), and Tau Ceti's
`TauCeti.SmoothTwoForm.contMDiff_interiorEquiv_symm_mpullback_prodMk` shows that such fields are
smooth in the parameter. The smooth one-form is given by
`TauCeti.SmoothTwoForm.exists_mpullback_prodMk_eq_mixedComponent`. On a single fibre over `x`
with `σ(x)` nondegenerate, `Xᵢ(x)` is thereby a smooth vector field, and Tau Ceti's
`TauCeti.SmoothBundleForm.contMDiff_eval₂` makes `σ(x)(Xᵢ(x), Xⱼ(x))` a smooth function.

The definition of `Xᵢ(x)` follows Tau Ceti's `TauCeti.SmoothTwoForm.hamiltonianVectorField`,
which also applies the inverse of a flat map to a covector. The statement of
`TauCeti.SmoothTwoForm.mixedVectorField_eq_iff`, and its proof, are adapted from Tau Ceti's
`TauCeti.SmoothTwoForm.hamiltonianVectorField_eq_iff_of_isInvertible_flat`.

The exterior derivative of a slice is read off `dτ` by Tau Ceti's
`TauCeti.mpullback_mextDeriv_at`, since the slice is the pull-back along `ι_x`, whose
derivative sends `w` to `(0, w)`.

The curl of the mixed components is Tau Ceti's
`TauCeti.SmoothForm.mextDeriv_apply_eq_fderiv_sub_fderiv_add_mvfderiv` rewritten in terms of the
components.

The formula for `dτ` follows the proof of Tau Ceti's
`TauCeti.SmoothForm.mextDeriv_apply_eq_fderiv_sub_fderiv_add_mvfderiv`, which evaluates `dτ` on
the product frame `(a, 0), (b, 0), (0, W)`, whose brackets all vanish. Here the frame is
`(0, W₁), (0, W₂), (∂ᵢ, 0)` for extensions `Wₖ` of `wₖ` to vector fields on `F`. One of its
brackets does not vanish, so the proof uses the invariant formula `TauCeti.mextDeriv_apply_two`
instead. That bracket is `[(0, W₁), (0, W₂)] = (0, [W₁, W₂])`, and the terms
along `F` make up `d_F αᵢ(x)(w₁, w₂)` by `TauCeti.mextDeriv_apply_one`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.3.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.RoughForm

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F] [ChartedSpace HF F]
  {ι : Type*} (τ : RoughForm (𝓘(ℝ, EB).prod IF) (EB × F) ℝ 2) (bs : Module.Basis ι ℝ EB)

/-- The **fibre component** of a two-form `τ` on `EB × F` over `x`: its slice `ι_x^* τ`, the
two-form on `F` obtained by pulling `τ` back along `y ↦ (x, y)`. -/
def fiberComponent (x : EB) : RoughForm IF F ℝ 2 :=
  mpullback IF (𝓘(ℝ, EB).prod IF) (Prod.mk x) τ

theorem fiberComponent_def (x : EB) :
    τ.fiberComponent x = mpullback IF (𝓘(ℝ, EB).prod IF) (Prod.mk x) τ :=
  (rfl)

/-- The fibre component of `τ` over `x` evaluates `τ` on vectors tangent to the fibre. -/
@[simp]
theorem fiberComponent_apply (x : EB) (y : F) (w₁ w₂ : TangentSpace IF y) :
    τ.fiberComponent x y ![w₁, w₂] = τ (x, y) ![((0 : EB), w₁), ((0 : EB), w₂)] := by
  rw [fiberComponent_def, mpullback_apply_pair, mfderiv_prodMk_right_apply,
    mfderiv_prodMk_right_apply]
  -- The two sides differ only in the type of the vectors, `TangentSpace` of the product or
  -- the product of the tangent spaces, which agree by definition.
  rfl

/-- The fibre component of a sum of two-forms is the sum of their fibre components. -/
@[simp]
theorem fiberComponent_add (σ : RoughForm (𝓘(ℝ, EB).prod IF) (EB × F) ℝ 2) (x : EB) :
    (τ + σ).fiberComponent x = τ.fiberComponent x + σ.fiberComponent x := by
  simp only [fiberComponent_def, mpullback_add]

/-- The fibre component of a difference of two-forms is the difference of their fibre
components. -/
@[simp]
theorem fiberComponent_sub (σ : RoughForm (𝓘(ℝ, EB).prod IF) (EB × F) ℝ 2) (x : EB) :
    (τ - σ).fiberComponent x = τ.fiberComponent x - σ.fiberComponent x := by
  simp only [fiberComponent_def, mpullback_sub]

/-- The fibre components of the zero two-form vanish. -/
@[simp]
theorem fiberComponent_zero (x : EB) :
    (0 : RoughForm (𝓘(ℝ, EB).prod IF) (EB × F) ℝ 2).fiberComponent x = 0 := by
  simp only [fiberComponent_def, mpullback_zero]

/-- The fibre component of `-τ` is minus that of `τ`. -/
@[simp]
theorem fiberComponent_neg (x : EB) : (-τ).fiberComponent x = -τ.fiberComponent x := by
  simp only [fiberComponent_def, mpullback_neg]

/-- The fibre component of `c • τ`, for a constant `c`, is `c` times that of `τ`. -/
@[simp]
theorem fiberComponent_smul (c : ℝ) (x : EB) :
    (c • τ).fiberComponent x = c • τ.fiberComponent x := by
  simp only [fiberComponent_def, mpullback_smul]

/-- Multiplying `τ` by a function `g` on `EB × F` multiplies its fibre component over `x`, at a
point `y` of `F`, by `g (x, y)`. -/
@[simp]
theorem fiberComponent_fun_smul (g : EB × F → ℝ) (x : EB) :
    fiberComponent (fun z ↦ g z • τ z) x = fun y ↦ g (x, y) • τ.fiberComponent x y := by
  rw [fiberComponent_def, mpullback_fun_smul, fiberComponent_def]

/-- Multiplying `τ` by a function `f` of the base point multiplies its fibre component over `x`
by `f x`. -/
theorem fiberComponent_fun_smul_fst (f : EB → ℝ) (x : EB) :
    fiberComponent (fun z ↦ f z.1 • τ z) x = f x • τ.fiberComponent x := by
  rw [fiberComponent_fun_smul]
  ext1 y
  rw [Pi.smul_apply]

/-- The exterior derivative of the fibre component of `τ` over `x` is that of `τ` on vectors
tangent to the fibre: on `w₁, w₂, u` at `y`, `d(σ(x))` takes the value of `dτ` at `(x, y)` on
`(0, w₁), (0, w₂), (0, u)`. The form `τ` need only be `C¹` at `(x, y)` as a section. -/
theorem mextDeriv_fiberComponent_apply [IsManifold IF 2 F] {x : EB} {y : F}
    (hτ : ContMDiffAt (𝓘(ℝ, EB).prod IF)
      ((𝓘(ℝ, EB).prod IF).prod 𝓘(ℝ, (EB × EF) [⋀^Fin 2]→L[ℝ] ℝ)) 1
      (fun z ↦ Bundle.TotalSpace.mk' ((EB × EF) [⋀^Fin 2]→L[ℝ] ℝ) z (τ z)) (x, y))
    (w₁ w₂ u : TangentSpace IF y) :
    mextDeriv (τ.fiberComponent x) y ![w₁, w₂, u] =
      mextDeriv τ (x, y) ![((0 : EB), w₁), ((0 : EB), w₂), ((0 : EB), u)] := by
  rw [fiberComponent_def,
    ← mpullback_mextDeriv_at (f := Prod.mk x) (contMDiffAt_const.prodMk contMDiffAt_id) hτ,
    mpullback_apply]
  congr 1
  funext i
  fin_cases i <;> exact mfderiv_prodMk_right_apply _

/-- The **mixed component** `αᵢ(x)` of a two-form `τ` on `EB × F`, for the basis `bs` of `EB`:
the one-form on `F` that is minus the slice over `x` of the contraction of `τ` with the constant
field `(bs i, 0)`. The sign is that of the local form `τ = σ + ∑ᵢ αᵢ ∧ dxᵢ + ⋯`
(`TauCeti.RoughForm.eq_verticalForm_add_sum`). -/
def mixedComponent (i : ι) (x : EB) : RoughForm IF F ℝ 1 :=
  -mpullback IF (𝓘(ℝ, EB).prod IF) (Prod.mk x)
    (τ.interior (Manifold.prodVectorField (fun x ↦ (bs i : TangentSpace 𝓘(ℝ, EB) x)) 0))

theorem mixedComponent_def (i : ι) (x : EB) :
    τ.mixedComponent bs i x = -mpullback IF (𝓘(ℝ, EB).prod IF) (Prod.mk x)
      (τ.interior (Manifold.prodVectorField (fun x ↦ (bs i : TangentSpace 𝓘(ℝ, EB) x)) 0)) :=
  (rfl)

/-- The mixed component `αᵢ(x)` evaluates `τ` on a vector tangent to the fibre followed by the
field `(bs i, 0)`. -/
@[simp]
theorem mixedComponent_apply (i : ι) (x : EB) (y : F) (w : TangentSpace IF y) :
    τ.mixedComponent bs i x y ![w] = τ (x, y) ![((0 : EB), w), (bs i, 0)] := by
  rw [mixedComponent_def, Pi.neg_apply, ContinuousAlternatingMap.neg_apply, mpullback_apply_one,
    interior_apply, mfderiv_prodMk_right_apply, neg_eq_iff_eq_neg]
  refine (congrArg (fun v : EB × EF ↦ τ (x, y) ![v, ((0 : EB), w)])
    (Manifold.prodVectorField_apply _ _ (x, y))).trans ?_
  exact (τ (x, y)).apply_vecCons_swap _ _

/-- The **mixed curl** of a two-form `τ` on `EB × F`, for the basis `bs` of `EB`: the value at
`w ∈ T_y F` of the one-form `∂ᵢαⱼ(x) - ∂ⱼαᵢ(x)` on `F`, where `αₖ` is the mixed component
`mixedComponent τ bs k` and `∂ₖ` differentiates in `x` along `bs k`. -/
def mixedCurl (i j : ι) (x : EB) (y : F) (w : TangentSpace IF y) : ℝ :=
  fderiv ℝ (fun x' ↦ τ.mixedComponent bs j x' y ![w]) x (bs i) -
    fderiv ℝ (fun x' ↦ τ.mixedComponent bs i x' y ![w]) x (bs j)

theorem mixedCurl_def (i j : ι) (x : EB) (y : F) (w : TangentSpace IF y) :
    τ.mixedCurl bs i j x y w =
      fderiv ℝ (fun x' ↦ τ.mixedComponent bs j x' y ![w]) x (bs i) -
        fderiv ℝ (fun x' ↦ τ.mixedComponent bs i x' y ![w]) x (bs j) :=
  (rfl)

/-- The mixed curl is antisymmetric in `i` and `j`. -/
theorem mixedCurl_swap (i j : ι) (x : EB) (y : F) (w : TangentSpace IF y) :
    τ.mixedCurl bs j i x y w = -τ.mixedCurl bs i j x y w := by
  rw [mixedCurl_def, mixedCurl_def, neg_sub]

/-- The mixed curl vanishes on the diagonal. -/
@[simp]
theorem mixedCurl_self (i : ι) (x : EB) (y : F) (w : TangentSpace IF y) :
    τ.mixedCurl bs i i x y w = 0 := by
  rw [mixedCurl_def, sub_self]

/-- The **base component** `f_{ij}(x)` of a two-form `τ` on `EB × F`, for the basis `bs` of
`EB`: the function on `F` whose value at `y` is `τ` at `(x, y)` on the fields `(bs i, 0)` and
`(bs j, 0)`. -/
def baseComponent (i j : ι) (x : EB) (y : F) : ℝ :=
  τ (x, y) ![(bs i, 0), (bs j, 0)]

@[simp]
theorem baseComponent_def (i j : ι) (x : EB) (y : F) :
    τ.baseComponent bs i j x y = τ (x, y) ![(bs i, 0), (bs j, 0)] :=
  (rfl)

/-- The value of `τ` on two copies of the vector `(bs i, 0)` vanishes. Its left side is what
`baseComponent_def` turns `f_{ii}(x)` at a point into, so `simp` proves that `f_{ii}(x)` vanishes
at each point. -/
@[simp]
theorem apply_basis_inl_self (i : ι) (x : EB) (y : F) : τ (x, y) ![(bs i, 0), (bs i, 0)] = 0 :=
  ContinuousAlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 1) rfl Fin.zero_ne_one

/-- The base components vanish on the diagonal: `f_{ii}(x)` is the zero function on `F`. -/
@[simp]
theorem baseComponent_self (i : ι) (x : EB) : τ.baseComponent bs i i x = 0 :=
  funext fun y ↦ by rw [baseComponent_def, apply_basis_inl_self, Pi.zero_apply]

/-- The base components are antisymmetric in the two indices. -/
theorem baseComponent_swap (i j : ι) (x : EB) (y : F) :
    τ.baseComponent bs j i x y = -τ.baseComponent bs i j x y :=
  ContinuousAlternatingMap.apply_vecCons_swap _ _ _

/-- **The local form of a two-form on a product.** A two-form `τ` on `EB × F` is the sum of the
vertical form of its fibre components `σ(x)`, of `∑ᵢ αᵢ ∧ dxᵢ` with its mixed components `αᵢ(x)`,
and of `∑_{i<j} f_{ij} dxᵢ ∧ dxⱼ` with its base components `f_{ij}(x)`, where `dxᵢ` is the
coordinate one-form of the basis `bs` of `EB`, pulled back along `Prod.fst`. -/
theorem eq_verticalForm_add_sum [FiniteDimensional ℝ EB] [Fintype ι] [LinearOrder ι] :
    τ = verticalForm 𝓘(ℝ, EB) τ.fiberComponent +
      ∑ i, (verticalForm 𝓘(ℝ, EB) (τ.mixedComponent bs i)).wedge
        (mpullback (𝓘(ℝ, EB).prod IF) 𝓘(ℝ, EB) Prod.fst (bs.coordOneForm i).val) +
      ∑ i, ∑ j with i < j, (fun z : EB × F ↦ τ.baseComponent bs i j z.1 z.2) •
        mpullback (𝓘(ℝ, EB).prod IF) 𝓘(ℝ, EB) Prod.fst
          (wedge (bs.coordOneForm i).val (bs.coordOneForm j).val) := by
  funext z
  refine ContinuousAlternatingMap.ext_fin_two fun v₁ v₂ ↦ ?_
  -- The components along `F` of tangent vectors of `EB × F`, as tangent vectors of `F`.
  have h₂ : (fun k ↦ (![v₁, v₂] k).2) = (![v₁.2, v₂.2] : Fin 2 → TangentSpace IF z.2) :=
    (FinVec.etaExpand_eq _).symm
  have h₁ : ∀ v : TangentSpace (𝓘(ℝ, EB).prod IF) z,
      (fun k ↦ (![v] k).2) = (![v.2] : Fin 1 → TangentSpace IF z.2) := fun _ ↦
    (FinVec.etaExpand_eq _).symm
  simp only [Pi.add_apply, ContinuousAlternatingMap.add_apply, Finset.sum_apply,
    ContinuousAlternatingMap.sum_apply, Pi.smul_apply', ContinuousAlternatingMap.smul_apply,
    mpullback_wedge, wedge_apply_one_one, verticalForm_apply, h₁, h₂,
    Module.Basis.mpullback_fst_coordOneForm_apply, baseComponent_def, smul_eq_mul,
    Matrix.cons_val_zero]
  refine ((τ z).apply_vecCons_prod_eq_sum bs v₁.1 v₂.1 v₁.2 v₂.2).trans ?_
  -- The fibre vectors are elements of `EF` on the left and of `TangentSpace IF z.2` on the right,
  -- so the components are matched term by term.
  congr 1
  · congr 1
    · exact (τ.fiberComponent_apply z.1 z.2 v₁.2 v₂.2).symm
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [τ.mixedComponent_apply bs i z.1 z.2 v₁.2, τ.mixedComponent_apply bs i z.1 z.2 v₂.2,
        smul_eq_mul, smul_eq_mul, mul_comm, mul_comm (bs.coord i v₁.1)]
      -- `τ (z.1, z.2)` and `τ z` agree by `Prod.mk_eta`, up to the types of the vectors.
      rfl
  · exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-! ### The derivative of the fibre components along the base -/

section FiberDeriv

open Bundle VectorField

variable [IsManifold IF 1 F]

/-- If `τ` is differentiable at `(x, y)`, then its slices `σ(x') = ι_{x'}^* τ`, read at `y`, are
differentiable in `x'` at `x`. -/
theorem differentiableAt_fiberComponent {x : EB} {y : F}
    (hτ : MDifferentiableAt (𝓘(ℝ, EB).prod IF)
      ((𝓘(ℝ, EB).prod IF).prod 𝓘(ℝ, (EB × EF) [⋀^Fin 2]→L[ℝ] ℝ))
      (fun z ↦ TotalSpace.mk' ((EB × EF) [⋀^Fin 2]→L[ℝ] ℝ) z (τ z)) (x, y)) :
    DifferentiableAt ℝ (fun x' ↦ τ.fiberComponent x' y) x := by
  have h := τ.differentiableWithinAt_range_inChartAt_of_mdifferentiableAt hτ
  have he : extChartAt (𝓘(ℝ, EB).prod IF) (x, y) (x, y) = (x, extChartAt IF y y) := by
    rw [extChartAt_prod]
    rfl
  rw [he] at h
  have hc : DifferentiableAt ℝ (fun x' : EB ↦ τ.inChartAt (x, y) (x', extChartAt IF y y)) x := by
    rw [← differentiableWithinAt_univ]
    refine DifferentiableWithinAt.comp (t := Set.range (𝓘(ℝ, EB).prod IF)) x ?_
      (differentiableAt_id.prodMk (differentiableAt_const _)).differentiableWithinAt ?_
    · exact h
    · intro x' _
      rw [ModelWithCorners.range_prod]
      exact ⟨by simp, Set.mem_range_self _⟩
  -- In the product chart at `(x, y)`, the slice over `x'` is read at the centre `e y` of the chart
  -- `e` of `F` at `y`.
  have heq (x' : EB) : τ.fiberComponent x' y =
      (τ.inChartAt (x, y) (x', extChartAt IF y y)).compContinuousLinearMap
        (ContinuousLinearMap.inr ℝ EB EF) := by
    rw [← (τ.fiberComponent x').inChartAt_extChartAt_self y, fiberComponent_def,
      TauCeti.inChartAt_mpullback_prodMk τ (x, y) (by simp) (mem_extChartAt_target y)]
    -- The chart of `EB` is the identity; the two sides then differ in the type of the slice.
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
    rfl
  simp_rw [heq]
  exact (ContinuousAlternatingMap.compContinuousLinearMapCLM
    (ContinuousLinearMap.inr ℝ EB EF)).differentiableAt.comp x hc

end FiberDeriv

/-- The **derivative of the fibre components** of a two-form `τ` on `EB × F` at `x` in the
direction `v ∈ EB`: the two-form on `F` whose value at `y` is the derivative at `x`, along `v`,
of the slices `x' ↦ σ(x') y`. For `v = bs i` it is the partial derivative `∂ᵢσ(x)`. -/
def fderivFiberComponent (x v : EB) : RoughForm IF F ℝ 2 :=
  fun y ↦ fderiv ℝ (fun x' ↦ τ.fiberComponent x' y) x v

theorem fderivFiberComponent_def (x v : EB) :
    τ.fderivFiberComponent x v = fun y ↦ fderiv ℝ (fun x' ↦ τ.fiberComponent x' y) x v :=
  (rfl)

/-- If `τ` is differentiable at `(x, y)`, then `∂_v σ(x)` evaluates at `y` to the derivative at
`x`, along `v`, of the values of `τ` at `(x', y)` on two vectors tangent to the fibre. -/
theorem fderivFiberComponent_apply [IsManifold IF 1 F] {x : EB} {y : F}
    (hτ : MDifferentiableAt (𝓘(ℝ, EB).prod IF)
      ((𝓘(ℝ, EB).prod IF).prod 𝓘(ℝ, (EB × EF) [⋀^Fin 2]→L[ℝ] ℝ))
      (fun z ↦ Bundle.TotalSpace.mk' ((EB × EF) [⋀^Fin 2]→L[ℝ] ℝ) z (τ z)) (x, y))
    (v : EB) (w₁ w₂ : TangentSpace IF y) :
    τ.fderivFiberComponent x v y ![w₁, w₂] =
      fderiv ℝ (fun x' ↦ τ (x', y) ![((0 : EB), w₁), ((0 : EB), w₂)]) x v := by
  -- The slices take values in `TangentSpace IF y [⋀^Fin 2]→L[ℝ] ℝ`, which is `EF [⋀^Fin 2]→L[ℝ] ℝ`
  -- with its norm only by unfolding `TangentSpace`; Mathlib's lemma needs the norm.
  have h := fderiv_continuousAlternatingMap_apply_const_apply (F := EF) (G := ℝ)
    (c := fun x' ↦ τ.fiberComponent x' y) (τ.differentiableAt_fiberComponent hτ) ![w₁, w₂] v
  refine h.symm.trans (congrArg (fderiv ℝ · x v) (funext fun x' ↦ ?_))
  exact τ.fiberComponent_apply x' y w₁ w₂

/-- If `τ` is `C^n` at `(x, y)`, then its mixed component `αᵢ(x)` is `C^n` at `y`. -/
theorem contMDiffAt_mixedComponent [IsManifold IF 1 F] {n : WithTop ℕ∞} (i : ι) {x : EB} {y : F}
    (hτ : ContMDiffAt (𝓘(ℝ, EB).prod IF)
      ((𝓘(ℝ, EB).prod IF).prod 𝓘(ℝ, (EB × EF) [⋀^Fin 2]→L[ℝ] ℝ)) n
      (fun z ↦ Bundle.TotalSpace.mk' ((EB × EF) [⋀^Fin 2]→L[ℝ] ℝ) z (τ z)) (x, y)) :
    ContMDiffAt IF (IF.prod 𝓘(ℝ, EF [⋀^Fin 1]→L[ℝ] ℝ)) n
      (fun y' ↦ Bundle.TotalSpace.mk' (EF [⋀^Fin 1]→L[ℝ] ℝ) y' (τ.mixedComponent bs i x y')) y := by
  set X := Manifold.prodVectorField (I := 𝓘(ℝ, EB)) (J := IF)
    (fun x : EB ↦ (bs i : TangentSpace 𝓘(ℝ, EB) x)) (0 : (y : F) → TangentSpace IF y)
  have hX : ContMDiffAt (𝓘(ℝ, EB).prod IF) (𝓘(ℝ, EB).prod IF).tangent n
      (fun z ↦ (X z : TangentBundle (𝓘(ℝ, EB).prod IF) (EB × F))) (x, y) :=
    Manifold.contMDiffAt_prodVectorField (contMDiff_tangentBundle_mk_const _).contMDiffAt
      (Bundle.contMDiff_zeroSection ℝ (TangentSpace IF)).contMDiffAt
  rw [mixedComponent_def]
  exact (ContMDiffAt.mpullback_form (RoughForm.contMDiffAt_interior hX hτ) (f := Prod.mk x)
    (n := ⊤) (contMDiffAt_const.prodMk contMDiffAt_id) le_top).neg_section

section Frame

open Bundle VectorField

variable [CompleteSpace EB] [CompleteSpace EF] [IsManifold IF 2 F]

/-- The invariant formula for `dτ` on the frame `(0, W₁)`, `(0, W₂)`, `(bs i, 0)` of `EB × F`,
for vector fields `W₁`, `W₂` on `F` differentiable at `y`, with its terms read as `∂ᵢσ(x)` and as
derivatives of `αᵢ(x)` along `F`. -/
private theorem mextDeriv_apply_prodVectorField (i : ι) {x : EB} {y : F}
    (hτ : ContMDiffAt (𝓘(ℝ, EB).prod IF)
      ((𝓘(ℝ, EB).prod IF).prod 𝓘(ℝ, (EB × EF) [⋀^Fin 2]→L[ℝ] ℝ)) 1
      (fun z ↦ TotalSpace.mk' ((EB × EF) [⋀^Fin 2]→L[ℝ] ℝ) z (τ z)) (x, y))
    {W₁ W₂ : (y : F) → TangentSpace IF y}
    (hW₁ : MDifferentiableAt IF IF.tangent (fun y ↦ (W₁ y : TangentBundle IF F)) y)
    (hW₂ : MDifferentiableAt IF IF.tangent (fun y ↦ (W₂ y : TangentBundle IF F)) y) :
    mextDeriv τ (x, y) ![((0 : EB), W₁ y), (0, W₂ y), (bs i, 0)] =
      τ.fderivFiberComponent x (bs i) y ![W₁ y, W₂ y] +
        (mvfderiv IF (fun y' ↦ τ.mixedComponent bs i x y' ![W₂ y']) y (W₁ y) -
          mvfderiv IF (fun y' ↦ τ.mixedComponent bs i x y' ![W₁ y']) y (W₂ y) -
          τ.mixedComponent bs i x y ![mlieBracket IF W₁ W₂ y]) := by
  have : IsManifold IF (minSmoothness ℝ 2) F := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have : IsManifold IF 1 F := .of_le (n := 2) (by norm_num)
  have hτ' := hτ.mdifferentiableAt one_ne_zero
  set U := Manifold.prodVectorField (I := 𝓘(ℝ, EB)) (J := IF)
    (0 : (x : EB) → TangentSpace 𝓘(ℝ, EB) x) W₁
  set V := Manifold.prodVectorField (I := 𝓘(ℝ, EB)) (J := IF)
    (0 : (x : EB) → TangentSpace 𝓘(ℝ, EB) x) W₂
  set X := Manifold.prodVectorField (I := 𝓘(ℝ, EB)) (J := IF)
    (fun x : EB ↦ (bs i : TangentSpace 𝓘(ℝ, EB) x)) (0 : (y : F) → TangentSpace IF y)
  have h0B : MDifferentiableAt 𝓘(ℝ, EB) 𝓘(ℝ, EB).tangent
      (fun x ↦ ((0 : (x : EB) → TangentSpace 𝓘(ℝ, EB) x) x : TangentBundle 𝓘(ℝ, EB) EB)) x :=
    (contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, EB))).mdifferentiableAt one_ne_zero
  have hcB : MDifferentiableAt 𝓘(ℝ, EB) 𝓘(ℝ, EB).tangent
      (fun x : EB ↦ (⟨x, bs i⟩ : TangentBundle 𝓘(ℝ, EB) EB)) x :=
    (contMDiff_tangentBundle_mk_const (n := 1) _).mdifferentiableAt one_ne_zero
  have hU : MDifferentiableAt (𝓘(ℝ, EB).prod IF) (𝓘(ℝ, EB).prod IF).tangent
      (fun z ↦ (U z : TangentBundle (𝓘(ℝ, EB).prod IF) (EB × F))) (x, y) :=
    Manifold.mdifferentiableAt_prodVectorField h0B hW₁
  have hV : MDifferentiableAt (𝓘(ℝ, EB).prod IF) (𝓘(ℝ, EB).prod IF).tangent
      (fun z ↦ (V z : TangentBundle (𝓘(ℝ, EB).prod IF) (EB × F))) (x, y) :=
    Manifold.mdifferentiableAt_prodVectorField h0B hW₂
  have hX : MDifferentiableAt (𝓘(ℝ, EB).prod IF) (𝓘(ℝ, EB).prod IF).tangent
      (fun z ↦ (X z : TangentBundle (𝓘(ℝ, EB).prod IF) (EB × F))) (x, y) :=
    Manifold.mdifferentiableAt_prodVectorField hcB
      ((contMDiff_zeroSection ℝ (TangentSpace IF)).mdifferentiableAt one_ne_zero)
  -- The values of the frame.
  have hU_apply (z : EB × F) : U z = ((0 : EB), W₁ z.2) := Manifold.prodVectorField_apply _ _ z
  have hV_apply (z : EB × F) : V z = ((0 : EB), W₂ z.2) := Manifold.prodVectorField_apply _ _ z
  have hX_apply (z : EB × F) : X z = (bs i, 0) := Manifold.prodVectorField_apply _ _ z
  -- The brackets of the frame: only `[(0, W₁), (0, W₂)] = (0, [W₁, W₂])` survives.
  have hUV : mlieBracket (𝓘(ℝ, EB).prod IF) U V (x, y) = ((0 : EB), mlieBracket IF W₁ W₂ y) := by
    rw [Manifold.mlieBracket_prodVectorField h0B h0B hW₁ hW₂]
    refine Prod.ext ?_ (Manifold.prodVectorField_snd _ _ _)
    -- The zero of `TangentSpace 𝓘(ℝ, EB) x` is that of `EB` only by unfolding `TangentSpace`.
    simp only [Manifold.prodVectorField_fst, mlieBracket_zero_left]
    rfl
  have hUX : mlieBracket (𝓘(ℝ, EB).prod IF) U X (x, y) = 0 := by
    rw [mlieBracket_swap_apply, neg_eq_zero]
    exact Manifold.mlieBracket_prodVectorField_horizontal_vertical hcB hW₁
  have hVX : mlieBracket (𝓘(ℝ, EB).prod IF) V X (x, y) = 0 := by
    rw [mlieBracket_swap_apply, neg_eq_zero]
    exact Manifold.mlieBracket_prodVectorField_horizontal_vertical hcB hW₂
  have h0 (v : TangentSpace (𝓘(ℝ, EB).prod IF) (x, y)) : τ (x, y) ![0, v] = 0 :=
    (τ (x, y)).map_coord_zero 0 rfl
  -- Each derivative along the frame is a derivative along `EB` or along `F`.
  have hdU := (mdifferentiableAt_apply_two hτ' hV hX).mvfderiv_prod_eq_add_apply (U (x, y))
  have hdV := (mdifferentiableAt_apply_two hτ' hU hX).mvfderiv_prod_eq_add_apply (V (x, y))
  have hdX := (mdifferentiableAt_apply_two hτ' hU hV).mvfderiv_prod_eq_add_apply (X (x, y))
  have hU1 : (U (x, y)).1 = (0 : TangentSpace 𝓘(ℝ, EB) (x, y).1) :=
    Manifold.prodVectorField_fst _ _ _
  have hV1 : (V (x, y)).1 = (0 : TangentSpace 𝓘(ℝ, EB) (x, y).1) :=
    Manifold.prodVectorField_fst _ _ _
  have hX2 : (X (x, y)).2 = (0 : TangentSpace IF (x, y).2) := Manifold.prodVectorField_snd _ _ _
  have hU2 : (U (x, y)).2 = (W₁ y : TangentSpace IF (x, y).2) := Manifold.prodVectorField_snd _ _ _
  have hV2 : (V (x, y)).2 = (W₂ y : TangentSpace IF (x, y).2) := Manifold.prodVectorField_snd _ _ _
  rw [hU1, map_zero, zero_add, hU2] at hdU
  rw [hV1, map_zero, zero_add, hV2] at hdV
  rw [hX2, map_zero, add_zero] at hdX
  -- The terms of the invariant formula, read on the slices through `(x, y)`. The `rfl`s close
  -- goals that differ by `(x, y).1 = x` or `(x, y).2 = y` and in the types of the vectors.
  have e₁ : (fun y' ↦ τ ((x, y).1, y') ![V ((x, y).1, y'), X ((x, y).1, y')]) =
      fun y' ↦ τ.mixedComponent bs i x y' ![W₂ y'] :=
    funext fun y' ↦ by rw [mixedComponent_apply, hV_apply, hX_apply]; rfl
  have e₂ : (fun y' ↦ τ ((x, y).1, y') ![U ((x, y).1, y'), X ((x, y).1, y')]) =
      fun y' ↦ τ.mixedComponent bs i x y' ![W₁ y'] :=
    funext fun y' ↦ by rw [mixedComponent_apply, hU_apply, hX_apply]; rfl
  have e₃ : (fun x' ↦ τ (x', (x, y).2) ![U (x', (x, y).2), V (x', (x, y).2)]) =
      fun x' ↦ τ (x', y) ![((0 : EB), W₁ y), ((0 : EB), W₂ y)] :=
    funext fun x' ↦ by rw [hU_apply, hV_apply]; rfl
  have e₄ : τ (x, y) ![mlieBracket (𝓘(ℝ, EB).prod IF) U V (x, y), X (x, y)] =
      τ.mixedComponent bs i x y ![mlieBracket IF W₁ W₂ y] := by
    rw [mixedComponent_apply, hUV, hX_apply]
    rfl
  have e₅ : mvfderiv 𝓘(ℝ, EB) (fun x' ↦ τ (x', y) ![((0 : EB), W₁ y), ((0 : EB), W₂ y)]) (x, y).1
      (X (x, y)).1 = τ.fderivFiberComponent x (bs i) y ![W₁ y, W₂ y] := by
    rw [hX_apply]
    exact (mvfderiv_eq_fderiv_apply _ _ _).trans (fderivFiberComponent_apply τ hτ' _ _ _).symm
  have hpt : ![U (x, y), V (x, y), X (x, y)] = (![((0 : EB), W₁ y), (0, W₂ y), (bs i, 0)] :
      Fin 3 → TangentSpace (𝓘(ℝ, EB).prod IF) (x, y)) := by
    rw [hU_apply, hV_apply, hX_apply]
    -- The two sides differ only by `(x, y).2 = y` and in the types of the entries.
    rfl
  rw [← hpt, mextDeriv_apply_two hτ' hU hV hX, hdU, hdV, hdX, hUX, hVX, h0, h0, e₁, e₂, e₃, e₄,
    e₅]
  abel

end Frame

/-- **The exterior derivative of `τ` on fibre vectors and a base field.** For a two-form `τ` on
`EB × F` that is `C¹` at `(x, y)`, vectors `w₁, w₂` tangent to `F` at `y` and the field `∂ᵢ`
of the basis `bs`,
`dτ((0, w₁), (0, w₂), (∂ᵢ, 0)) = ∂ᵢσ(x)(w₁, w₂) + d_F αᵢ(x)(w₁, w₂)`,
where `∂ᵢσ(x)` differentiates the fibre components along `∂ᵢ` and `d_F αᵢ(x)` is the exterior
derivative on `F` of the mixed component. -/
theorem mextDeriv_apply_eq_fderivFiberComponent_add_mextDeriv_mixedComponent [CompleteSpace EB]
    [CompleteSpace EF] [IsManifold IF 2 F] (i : ι) {x : EB} {y : F}
    (hτ : ContMDiffAt (𝓘(ℝ, EB).prod IF)
      ((𝓘(ℝ, EB).prod IF).prod 𝓘(ℝ, (EB × EF) [⋀^Fin 2]→L[ℝ] ℝ)) 1
      (fun z ↦ Bundle.TotalSpace.mk' ((EB × EF) [⋀^Fin 2]→L[ℝ] ℝ) z (τ z)) (x, y))
    (w₁ w₂ : TangentSpace IF y) :
    mextDeriv τ (x, y) ![((0 : EB), w₁), (0, w₂), (bs i, 0)] =
      τ.fderivFiberComponent x (bs i) y ![w₁, w₂] +
        mextDeriv (τ.mixedComponent bs i x) y ![w₁, w₂] := by
  have : IsManifold IF 1 F := .of_le (n := 2) (by norm_num)
  -- Extend `w₁` and `w₂` to vector fields on `F` and apply the invariant formula on `F`.
  have hW₁ := FiberBundle.mdifferentiableAt_extend IF EF w₁
  have hW₂ := FiberBundle.mdifferentiableAt_extend IF EF w₂
  have h := τ.mextDeriv_apply_prodVectorField bs i hτ hW₁ hW₂
  rw [← mextDeriv_apply_one ((τ.contMDiffAt_mixedComponent bs i hτ).mdifferentiableAt
    one_ne_zero) hW₁ hW₂, FiberBundle.extend_apply_self, FiberBundle.extend_apply_self] at h
  exact h

/-- **The exterior derivative of `τ` on two fibre vectors.** For a two-form `τ` on `EB × F` that
is `C¹` at `(x, y)`, vectors `w₁, w₂` tangent to `F` at `y` and any `v = (a, u)` tangent to
`EB × F` there, with `a = ∑ᵢ cᵢ bs i` in the basis `bs`,
`dτ((0, w₁), (0, w₂), v) = d(σ(x))(w₁, w₂, u) + ∑ᵢ cᵢ (∂ᵢσ(x) + d_F αᵢ(x))(w₁, w₂)`. -/
theorem mextDeriv_apply_eq_mextDeriv_fiberComponent_add_sum [CompleteSpace EB]
    [CompleteSpace EF] [IsManifold IF 2 F] {x : EB} {y : F}
    (hτ : ContMDiffAt (𝓘(ℝ, EB).prod IF)
      ((𝓘(ℝ, EB).prod IF).prod 𝓘(ℝ, (EB × EF) [⋀^Fin 2]→L[ℝ] ℝ)) 1
      (fun z ↦ Bundle.TotalSpace.mk' ((EB × EF) [⋀^Fin 2]→L[ℝ] ℝ) z (τ z)) (x, y))
    (w₁ w₂ : TangentSpace IF y) (v : TangentSpace (𝓘(ℝ, EB).prod IF) (x, y)) :
    mextDeriv τ (x, y) ![((0 : EB), w₁), (0, w₂), v] =
      mextDeriv (τ.fiberComponent x) y ![w₁, w₂, v.2] +
        (bs.repr v.1).sum fun i c ↦
          c * (τ.fderivFiberComponent x (bs i) y ![w₁, w₂] +
            mextDeriv (τ.mixedComponent bs i x) y ![w₁, w₂]) := by
  -- `dτ` at `(x, y)` with the first two vectors fixed, as a linear map of the third.
  -- The tangent space of `EB × F` at `(x, y)` is `EB × EF`, where the splitting below lives.
  let f : (EB × EF) [⋀^Fin 3]→L[ℝ] ℝ := mextDeriv τ (x, y)
  let L := f.toContinuousMultilinearMap.toContinuousLinearMap ![((0 : EB), w₁), (0, w₂), 0] 2
  have hL (u : EB × EF) : mextDeriv τ (x, y) ![((0 : EB), w₁), (0, w₂), u] = L u := by
    rw [ContinuousMultilinearMap.toContinuousLinearMap_apply,
      ContinuousAlternatingMap.coe_toContinuousMultilinearMap]
    exact congrArg _ (funext fun k ↦ by fin_cases k <;> rfl)
  -- Split the third vector along the fibre and along the basis of `EB`.
  have hv : (v : EB × EF) =
      ((0 : EB), v.2) + (bs.repr v.1).sum fun i c ↦ c • ((bs i, 0) : EB × EF) := by
    refine Prod.ext ?_ ?_
    · simpa [Finsupp.sum, Prod.fst_sum, Finsupp.linearCombination_apply] using
        (bs.linearCombination_repr v.1).symm
    · simp [Finsupp.sum, Prod.snd_sum]
  rw [hL v, congrArg L hv, L.map_add, map_finsuppSum, ← hL]
  -- The fibre vectors are elements of `EF` here and of `TangentSpace IF y` in the lemmas on the
  -- components, so the terms are matched up to that identification.
  refine congrArg₂ (· + ·) (τ.mextDeriv_fiberComponent_apply hτ w₁ w₂ v.2).symm
    (Finsupp.sum_congr fun i _ ↦ ?_)
  rw [map_smul, ← hL, smul_eq_mul]
  exact congrArg _
    (τ.mextDeriv_apply_eq_fderivFiberComponent_add_mextDeriv_mixedComponent bs i hτ w₁ w₂)

/-! ### Vertical closedness in a chart -/

section VerticallyClosed

variable [CompleteSpace EB] [CompleteSpace EF] [IsManifold IF 2 F]

/-- **Vertical closedness at a point of a chart.** For a two-form `τ` on `EB × F` that is `C¹` at
`(x, y)`, the exterior derivative `dτ` vanishes at `(x, y)` on every triple whose first two
vectors are vertical for the first projection exactly when `d(σ(x))` vanishes at `y` and
`∂ᵢσ(x) + d_F αᵢ(x)` vanishes at `y` for every `i`. -/
theorem isVerticallyClosedOn_singleton_iff_local {x : EB} {y : F}
    (hτ : ContMDiffAt (𝓘(ℝ, EB).prod IF)
      ((𝓘(ℝ, EB).prod IF).prod 𝓘(ℝ, (EB × EF) [⋀^Fin 2]→L[ℝ] ℝ)) 1
      (fun z ↦ Bundle.TotalSpace.mk' ((EB × EF) [⋀^Fin 2]→L[ℝ] ℝ) z (τ z)) (x, y)) :
    τ.IsVerticallyClosedOn 𝓘(ℝ, EB) Prod.fst {(x, y)} ↔
      mextDeriv (τ.fiberComponent x) y = 0 ∧
        ∀ i, τ.fderivFiberComponent x (bs i) y + mextDeriv (τ.mixedComponent bs i x) y = 0 := by
  rw [isVerticallyClosedOn_iff]
  refine ⟨fun h ↦ ⟨?_, fun i ↦ ?_⟩, fun hh z hz η₁ hη₁ η₂ hη₂ v ↦ ?_⟩
  · refine ContinuousAlternatingMap.ext fun u ↦ ?_
    have hu : u = ![u 0, u 1, u 2] := (FinVec.etaExpand_eq u).symm
    rw [hu, τ.mextDeriv_fiberComponent_apply hτ]
    exact h (x, y) rfl _ (mem_ker_mfderiv_fst_iff.2 rfl) _ (mem_ker_mfderiv_fst_iff.2 rfl) _
  · refine ContinuousAlternatingMap.ext_fin_two fun w₁ w₂ ↦ ?_
    rw [ContinuousAlternatingMap.add_apply,
      ← τ.mextDeriv_apply_eq_fderivFiberComponent_add_mextDeriv_mixedComponent bs i hτ]
    exact h (x, y) rfl _ (mem_ker_mfderiv_fst_iff.2 rfl) _ (mem_ker_mfderiv_fst_iff.2 rfl) _
  · obtain ⟨h₀, h⟩ := hh
    obtain rfl : z = (x, y) := hz
    rw [mem_ker_mfderiv_fst_iff] at hη₁ hη₂
    have hη₁' : η₁ = ((0 : EB), η₁.2) := Prod.ext hη₁ rfl
    have hη₂' : η₂ = ((0 : EB), η₂.2) := Prod.ext hη₂ rfl
    rw [hη₁', hη₂']
    refine (τ.mextDeriv_apply_eq_mextDeriv_fiberComponent_add_sum bs hτ η₁.2 η₂.2 v).trans ?_
    simp only [h₀, ← ContinuousAlternatingMap.add_apply, h]
    simp

/-- **Vertical closedness in a chart.** Let `U` be open in `EB` and `τ` a two-form on `EB × F`
that is `C¹` on `U ×ˢ univ`. Then `τ` is vertically closed on `U ×ˢ univ` for the first
projection exactly when, for every `x ∈ U`, the fibre component `σ(x)` is closed and
`∂ᵢσ(x) + d_F αᵢ(x) = 0` for every `i`, where `∂ᵢσ(x)` is the derivative of the fibre
components along `bs i` and `αᵢ(x)` the mixed component. -/
theorem isVerticallyClosed_iff_local {U : Set EB} (hU : IsOpen U)
    (hτ : ContMDiffOn (𝓘(ℝ, EB).prod IF)
      ((𝓘(ℝ, EB).prod IF).prod 𝓘(ℝ, (EB × EF) [⋀^Fin 2]→L[ℝ] ℝ)) 1
      (fun z ↦ Bundle.TotalSpace.mk' ((EB × EF) [⋀^Fin 2]→L[ℝ] ℝ) z (τ z)) (U ×ˢ Set.univ)) :
    τ.IsVerticallyClosedOn 𝓘(ℝ, EB) Prod.fst (U ×ˢ Set.univ) ↔
      ∀ x ∈ U, mextDeriv (τ.fiberComponent x) = 0 ∧
        ∀ i, τ.fderivFiberComponent x (bs i) + mextDeriv (τ.mixedComponent bs i x) = 0 := by
  have hτ' {x : EB} (hx : x ∈ U) (y : F) := τ.isVerticallyClosedOn_singleton_iff_local bs
    (hτ.contMDiffAt ((hU.prod isOpen_univ).mem_nhds (Set.mk_mem_prod hx (Set.mem_univ y))))
  refine ⟨fun h x hx ↦ ⟨funext fun y ↦ ?_, fun i ↦ funext fun y ↦ ?_⟩,
    fun h ↦ isVerticallyClosedOn_iff.2 ?_⟩
  · exact ((hτ' hx y).1 (h.mono (Set.singleton_subset_iff.2 ⟨hx, Set.mem_univ y⟩))).1
  · exact ((hτ' hx y).1 (h.mono (Set.singleton_subset_iff.2 ⟨hx, Set.mem_univ y⟩))).2 i
  · rintro ⟨x, y⟩ ⟨hx, -⟩
    exact isVerticallyClosedOn_iff.1 ((hτ' hx y).2
      ⟨congrFun (h x hx).1 y, fun i ↦ congrFun ((h x hx).2 i) y⟩) (x, y) rfl

end VerticallyClosed

end TauCeti.RoughForm

namespace TauCeti.SmoothTwoForm

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F]
  {ι : Type*} (τ : SmoothTwoForm (𝓘(ℝ, EB).prod IF) (EB × F)) (bs : Module.Basis ι ℝ EB)

/-- The fibre component `σ(x)` of a smooth two-form `τ` on `EB × F`, as a smooth two-form on
`F`: the pull-back of `τ` along `y ↦ (x, y)`. -/
def smoothFiberComponent (x : EB) : SmoothTwoForm IF F :=
  SmoothForm.mpullback (Prod.mk x) (contMDiff_const.prodMk contMDiff_id) τ

theorem smoothFiberComponent_def (x : EB) :
    τ.smoothFiberComponent x =
      SmoothForm.mpullback (Prod.mk x) (contMDiff_const.prodMk contMDiff_id) τ :=
  (rfl)

@[simp]
theorem coe_smoothFiberComponent (x : EB) :
    (τ.smoothFiberComponent x).val = RoughForm.fiberComponent τ.val x := by
  rw [smoothFiberComponent_def, SmoothForm.coe_mpullback, RoughForm.fiberComponent_def]

/-- The smooth fibre component of `τ` over `x` evaluates `τ` on vectors tangent to the fibre. -/
theorem eval₂_smoothFiberComponent (x : EB) (y : F) (w₁ w₂ : TangentSpace IF y) :
    SmoothBundleForm.eval₂ (τ.smoothFiberComponent x) y w₁ w₂ =
      τ.val (x, y) ![((0 : EB), w₁), ((0 : EB), w₂)] := by
  rw [SmoothBundleForm.eval₂_apply, coe_smoothFiberComponent, RoughForm.fiberComponent_apply]

/-- The vector field `Xᵢ(x)` on `F` dual to the mixed component `αᵢ(x)` through the fibre
component `σ(x)`: its value at `y` is the inverse of the flat map of `σ(x)` at `y` applied to
`αᵢ(x)` at `y`. Where `σ(x)` is nondegenerate, it is the vector field with `ι(Xᵢ(x)) σ(x) = αᵢ(x)`
(`TauCeti.SmoothTwoForm.eval₂_mixedVectorField`). -/
def mixedVectorField (i : ι) (x : EB) (y : F) : TangentSpace IF y :=
  ((τ.smoothFiberComponent x).flat y).inverse
    ((ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace IF y) ℝ (0 : Fin 1)).symm
      (RoughForm.mixedComponent τ.val bs i x y))

theorem mixedVectorField_def (i : ι) (x : EB) (y : F) :
    τ.mixedVectorField bs i x y = ((τ.smoothFiberComponent x).flat y).inverse
      ((ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace IF y) ℝ (0 : Fin 1)).symm
        (RoughForm.mixedComponent τ.val bs i x y)) :=
  (rfl)

/-- Where the fibre component `σ(x)` is nondegenerate, `Xᵢ(x)(y)` is the unique tangent vector
`v` at `y` with `σ(x)(v, w) = αᵢ(x)(w)` for every `w`. -/
theorem mixedVectorField_eq_iff [FiniteDimensional ℝ EF] {x : EB}
    (hσ : (τ.smoothFiberComponent x).IsNondegenerate) (i : ι) (y : F) {v : TangentSpace IF y} :
    τ.mixedVectorField bs i x y = v ↔
      ∀ w, SmoothBundleForm.eval₂ (τ.smoothFiberComponent x) y v w =
        RoughForm.mixedComponent τ.val bs i x y ![w] := by
  rw [mixedVectorField_def, (hσ.isInvertible_flat y).inverse_apply_eq,
    ContinuousLinearMap.ext_iff]
  exact forall_congr' fun w ↦ by
    rw [flat_apply, ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply,
      Matrix.vec_single_eq_const, eq_comm]

/-- Where the fibre component `σ(x)` is nondegenerate, the contraction of `σ(x)` with the vector
field `Xᵢ(x)` is the mixed component `αᵢ(x)`: `σ(x)(Xᵢ(x), w) = αᵢ(x)(w)`. -/
theorem eval₂_mixedVectorField [FiniteDimensional ℝ EF] {x : EB}
    (hσ : (τ.smoothFiberComponent x).IsNondegenerate) (i : ι) (y : F) (w : TangentSpace IF y) :
    SmoothBundleForm.eval₂ (τ.smoothFiberComponent x) y (τ.mixedVectorField bs i x y) w =
      RoughForm.mixedComponent τ.val bs i x y ![w] :=
  (τ.mixedVectorField_eq_iff bs hσ i y).1 rfl w

/-- Let `α` be a smooth one-form on `EB × F` whose slice over `x` is `αᵢ(x)`. Where the fibre
component `σ(x)` is nondegenerate, `Xᵢ(x)` agrees at every point with the smooth vector field
`(σ(x)♭)⁻¹` of that slice, the inverse of Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv` of `σ(x)` applied to it. -/
theorem mixedVectorField_eq_interiorEquiv_symm [FiniteDimensional ℝ EF] {x : EB}
    (hσ : (τ.smoothFiberComponent x).IsNondegenerate) (i : ι)
    {α : SmoothForm (𝓘(ℝ, EB).prod IF) (EB × F) ℝ 1}
    (hα : (SmoothForm.mpullback (Prod.mk x) (contMDiff_const.prodMk contMDiff_id) α).val =
      RoughForm.mixedComponent τ.val bs i x) (y : F) :
    τ.mixedVectorField bs i x y = hσ.interiorEquiv.symm
      (SmoothForm.mpullback (Prod.mk x) (contMDiff_const.prodMk contMDiff_id) α) y := by
  refine (τ.mixedVectorField_eq_iff bs hσ i y).2 fun w ↦ ?_
  rw [← flat_apply, IsNondegenerate.interiorEquiv_symm_apply,
    (hσ.isInvertible_flat y).self_apply_inverse, SmoothForm.degreeOneEquiv_apply_apply, hα,
    Matrix.vec_single_eq_const]

/-- Where the fibre component `σ(x)` is nondegenerate, the vector `(bs i, Xᵢ(x)(y))` at `(x, y)`
is horizontal for `τ` and the first projection. -/
theorem mk_mixedVectorField_mem_horizontalDistribution [FiniteDimensional ℝ EF] {x : EB}
    (hσ : (τ.smoothFiberComponent x).IsNondegenerate) (i : ι) (y : F) :
    (Manifold.tangentSpaceProdEquiv (x, y)).symm (bs i, τ.mixedVectorField bs i x y) ∈
      horizontalDistribution 𝓘(ℝ, EB) Prod.fst τ (x, y) := by
  set e := Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ, EB)) (J := IF) (x, y)
  refine mem_horizontalDistribution_iff.2 fun η hη ↦ ?_
  rw [mem_ker_mfderiv_fst_iff] at hη
  have hη' : η = ((0 : EB), η.2) := Prod.ext hη rfl
  -- The pairs as vectors of the tangent space of `EB × F`, for `h` and `hs` below.
  have he (a : EB) (b : TangentSpace IF y) : e.symm (a, b) = ((a, b) : EB × EF) :=
    Manifold.tangentSpaceProdEquiv_symm_apply _ _
  have hsplit : e.symm (bs i, τ.mixedVectorField bs i x y) =
      e.symm (bs i, 0) + e.symm ((0 : EB), τ.mixedVectorField bs i x y) := by
    rw [← map_add]
    exact congrArg e.symm (Prod.ext (add_zero _).symm (zero_add _).symm)
  have h := ((τ.eval₂_smoothFiberComponent x y _ _).symm.trans
    (τ.eval₂_mixedVectorField bs hσ i y η.2)).trans
    (RoughForm.mixedComponent_apply τ.val bs i x y η.2)
  have hs := (τ.val (x, y)).apply_vecCons_swap ((0 : EB), η.2)
    ((0 : EB), τ.mixedVectorField bs i x y)
  rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply, hsplit,
    (τ.val (x, y)).apply_vecCons_add_right, he, he, hη']
  exact add_eq_zero_iff_eq_neg.2 (h.symm.trans hs)

/-- **The horizontal lift in a chart.** Where the fibre component `σ(x)` is nondegenerate, the
horizontal lift of the basis vector `bs i` at `(x, y)` for the connection of `τ` on the first
projection `EB × F → EB` is `(bs i, Xᵢ(x)(y))`, where `Xᵢ(x)` is the vector field on `F` with
`ι(Xᵢ(x)) σ(x) = αᵢ(x)`. -/
theorem horizontalLift_local [FiniteDimensional ℝ EF] {n : ℕ∞ω}
    (hD : IsEhresmannConnection (𝓘(ℝ, EB).prod IF) 𝓘(ℝ, EB) n Prod.fst
      (horizontalDistribution 𝓘(ℝ, EB) Prod.fst τ)) {x : EB}
    (hσ : (τ.smoothFiberComponent x).IsNondegenerate) (i : ι) (y : F) :
    (hD.horizontalLift (x, y) (bs i) : TangentSpace (𝓘(ℝ, EB).prod IF) (x, y)) =
      (Manifold.tangentSpaceProdEquiv (x, y)).symm (bs i, τ.mixedVectorField bs i x y) := by
  refine (congrArg Subtype.val (hD.eq_horizontalLift_iff
    (w := ⟨_, τ.mk_mixedVectorField_mem_horizontalDistribution bs hσ i y⟩) |>.2 ?_)).symm
  exact (mfderiv_fst_apply (x, y) _).trans
    (congrArg Prod.fst
      (Manifold.tangentSpaceProdEquiv_symm_apply (I := 𝓘(ℝ, EB)) (J := IF) (x, y) _))

/-- A two-form `τ` on `EB × F` is vertically nondegenerate for the first projection exactly when
each of its fibre components `σ(x)` is nondegenerate. -/
theorem isVerticallyNondegenerate_fst_iff :
    IsVerticallyNondegenerate 𝓘(ℝ, EB) Prod.fst τ ↔
      ∀ x, (τ.smoothFiberComponent x).IsNondegenerate := by
  simp only [isVerticallyNondegenerate_iff_forall, isNondegenerate_iff_separatingLeft,
    mem_ker_mfderiv_fst_iff, Prod.forall,
    SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply, coe_smoothFiberComponent,
    RoughForm.fiberComponent_apply]
  refine ⟨fun h x y v hv ↦ ?_, fun h x y u hu hτ ↦ ?_⟩
  · refine congrArg Prod.snd (h x y ((0 : EB), v) rfl fun w hw ↦ ?_ : ((0 : EB), v) = 0)
    have hw' : w = ((0 : EB), w.2) := Prod.ext hw rfl
    rw [hw']
    exact hv w.2
  · have hu' : u = ((0 : EB), u.2) := Prod.ext hu rfl
    refine hu'.trans (Prod.ext rfl (h x y u.2 fun w ↦ ?_))
    have := hτ ((0 : EB), w) rfl
    rw [hu'] at this
    exact this

/-- The constant vector field `(bs k, 0)` on `EB × F`, as a smooth section of the tangent
bundle. -/
def _root_.SymplecticGeometry.baseField (k : ι) :
    Cₛ^∞⟮𝓘(ℝ, EB).prod IF; EB × EF, TangentSpace (𝓘(ℝ, EB).prod IF) (M := EB × F)⟯ :=
  ⟨Manifold.prodVectorField (fun x ↦ (bs k : TangentSpace 𝓘(ℝ, EB) x)) 0,
    Manifold.contMDiff_prodVectorField (contMDiff_vectorSpace_iff_contDiff.2 contDiff_const)
      (Bundle.contMDiff_zeroSection ℝ (TangentSpace IF (M := F)))⟩

/-- The underlying field of `baseField bs k` is the product field of the constant field `bs k` of
`EB` and the zero field of `F`. -/
theorem _root_.SymplecticGeometry.coe_baseField (k : ι) :
    ⇑(SymplecticGeometry.baseField (IF := IF) (F := F) bs k) =
      Manifold.prodVectorField (fun x ↦ (bs k : TangentSpace 𝓘(ℝ, EB) x))
        (0 : (y : F) → TangentSpace IF y) :=
  (rfl)

@[simp]
theorem _root_.SymplecticGeometry.baseField_apply (k : ι) (p : EB × F) :
    SymplecticGeometry.baseField (IF := IF) bs k p = ((bs k, 0) : EB × EF) :=
  Manifold.prodVectorField_apply _ _ p

/-- The mixed components `αᵢ(x)` are, for all `x` at once, the slices of one smooth one-form on
`EB × F`, namely minus the contraction of `τ` with the constant field `(bs i, 0)`. -/
theorem exists_mpullback_prodMk_eq_mixedComponent (i : ι) :
    ∃ α : SmoothForm (𝓘(ℝ, EB).prod IF) (EB × F) ℝ 1, ∀ x : EB,
      (SmoothForm.mpullback (Prod.mk x) (contMDiff_const.prodMk contMDiff_id) α).val =
        RoughForm.mixedComponent τ.val bs i x := by
  refine ⟨-SmoothForm.interiorProduct (SymplecticGeometry.baseField bs i) τ, fun x ↦ ?_⟩
  rw [map_neg, NegMemClass.coe_neg, SmoothForm.coe_mpullback, SmoothForm.coe_interiorProduct,
    RoughForm.mixedComponent_def, SymplecticGeometry.coe_baseField]

/-- **The vector fields `Xᵢ` are smooth.** If every fibre component `σ(x)` is nondegenerate,
the vector field `Xᵢ(x)` on `F` with `ι(Xᵢ(x)) σ(x) = αᵢ(x)` is smooth jointly in `x` and the
point of `F`. -/
theorem contMDiff_mixedVectorField [FiniteDimensional ℝ EF]
    (hσ : ∀ x, (τ.smoothFiberComponent x).IsNondegenerate) (i : ι) :
    ContMDiff (𝓘(ℝ, EB).prod IF) IF.tangent ∞
      (fun p : EB × F ↦ (⟨p.2, τ.mixedVectorField bs i p.1 p.2⟩ : TangentBundle IF F)) := by
  obtain ⟨α, hα⟩ := τ.exists_mpullback_prodMk_eq_mixedComponent bs i
  refine (contMDiff_interiorEquiv_symm_mpullback_prodMk τ hσ α).congr fun p ↦ ?_
  exact congrArg (Bundle.TotalSpace.mk p.2)
    (τ.mixedVectorField_eq_interiorEquiv_symm bs (hσ p.1) i (hα p.1) p.2)

/-- **The vector field `Xᵢ(x)` is smooth.** Where the fibre component `σ(x)` is nondegenerate,
the vector field `Xᵢ(x)` on `F` with `ι(Xᵢ(x)) σ(x) = αᵢ(x)` is smooth. -/
theorem contMDiff_mixedVectorField_of_isNondegenerate [FiniteDimensional ℝ EF] {x : EB}
    (hσ : (τ.smoothFiberComponent x).IsNondegenerate) (i : ι) :
    ContMDiff IF IF.tangent ∞
      (fun y : F ↦ (⟨y, τ.mixedVectorField bs i x y⟩ : TangentBundle IF F)) := by
  obtain ⟨α, hα⟩ := τ.exists_mpullback_prodMk_eq_mixedComponent bs i
  exact (hσ.interiorEquiv.symm _).contMDiff.congr fun y ↦
    congrArg (Bundle.TotalSpace.mk y) (τ.mixedVectorField_eq_interiorEquiv_symm bs hσ i (hα x) y)

/-- Where the fibre component `σ(x)` is nondegenerate, the function `y ↦ σ(x)(Xᵢ(x), Xⱼ(x))` on
`F` is smooth. -/
theorem contMDiff_eval₂_mixedVectorField [FiniteDimensional ℝ EF] {x : EB}
    (hσ : (τ.smoothFiberComponent x).IsNondegenerate) (i j : ι) :
    ContMDiff IF 𝓘(ℝ) ∞ (fun y ↦ SmoothBundleForm.eval₂ (τ.smoothFiberComponent x) y
      (τ.mixedVectorField bs i x y) (τ.mixedVectorField bs j x y)) := fun y ↦ by
  have h := ((τ.smoothFiberComponent x).contMDiff_eval₂ (b := id)
    (τ.contMDiff_mixedVectorField_of_isNondegenerate bs hσ i)
    (τ.contMDiff_mixedVectorField_of_isNondegenerate bs hσ j)) y
  rw [Bundle.contMDiffAt_totalSpace_iff] at h
  simpa [Bundle.Trivial.fiberBundle_trivializationAt'] using h.2

open SymplecticGeometry in
/-- The base components `f_{ij}(x)(y) = τ((bs i, 0), (bs j, 0))` of a smooth two-form `τ` on
`EB × F` are smooth jointly in `x` and `y`. -/
theorem contMDiff_baseComponent (i j : ι) :
    ContMDiff (𝓘(ℝ, EB).prod IF) 𝓘(ℝ) ∞
      fun p : EB × F ↦ RoughForm.baseComponent τ.val bs i j p.1 p.2 := by
  refine (SmoothForm.interiorProduct (baseField bs j)
    (SmoothForm.interiorProduct (baseField bs i) τ)).contMDiff_apply_zero.congr fun p ↦ ?_
  rw [RoughForm.baseComponent_def, SmoothForm.coe_interiorProduct, RoughForm.interior_apply,
    SmoothForm.coe_interiorProduct, RoughForm.interior_apply, baseField_apply, baseField_apply]
  congr 1
  ext k
  fin_cases k <;> rfl

section Curl

variable [CompleteSpace EB] [CompleteSpace EF]

/-- **The curl of the mixed components.** For a smooth two-form `τ` on `EB × F`, with mixed
components `αₖ` and base components `f_{ij}` for the basis `bs`, and a vector `w` tangent to `F`
at `y`, `∂ᵢαⱼ(x)(w) - ∂ⱼαᵢ(x)(w) = d_F f_{ij}(x)(w) - dτ((bs i, 0), (bs j, 0), (0, w))`, where
`∂ₖ` differentiates in `x` along `bs k`. -/
theorem fderiv_mixedComponent_sub_fderiv_mixedComponent (i j : ι) (x : EB) (y : F)
    (w : TangentSpace IF y) :
    fderiv ℝ (fun x' ↦ RoughForm.mixedComponent τ.val bs j x' y ![w]) x (bs i) -
        fderiv ℝ (fun x' ↦ RoughForm.mixedComponent τ.val bs i x' y ![w]) x (bs j) =
      mvfderiv IF (RoughForm.baseComponent τ.val bs i j x) y w -
        mextDeriv τ.val (x, y) ![(bs i, 0), (bs j, 0), ((0 : EB), w)] := by
  have hα (k : ι) : (fun x' ↦ RoughForm.mixedComponent τ.val bs k x' y ![w]) =
      fun x' ↦ -τ.val (x', y) ![(bs k, 0), ((0 : EB), w)] := by
    funext x'
    rw [RoughForm.mixedComponent_apply]
    exact (τ.val (x', y)).apply_vecCons_swap _ _
  have hf : RoughForm.baseComponent τ.val bs i j x =
      fun y' ↦ τ.val (x, y') ![(bs i, 0), (bs j, 0)] :=
    funext fun _ ↦ RoughForm.baseComponent_def ..
  rw [hα, hα, fderiv_fun_neg, fderiv_fun_neg, neg_apply, neg_apply, hf,
    SmoothForm.mextDeriv_apply_eq_fderiv_sub_fderiv_add_mvfderiv]
  abel

end Curl

end TauCeti.SmoothTwoForm
