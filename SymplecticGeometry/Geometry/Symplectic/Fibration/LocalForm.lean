/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Vertical
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
public import TauCeti.Geometry.Manifold.VectorField.Prod
import SymplecticGeometry.Algebra.BigOperators.Pairs
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Topology.Algebra.Module.Alternating.Basic

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

## Main definitions

* `Module.Basis.coordOneForm bs i`: the constant one-form `dxᵢ` on `EB`.
* `TauCeti.RoughForm.fiberComponent τ x`: the slice of `τ` over `x`.
* `TauCeti.RoughForm.mixedComponent τ bs i x`: the one-form `αᵢ(x)` on `F`.
* `TauCeti.RoughForm.baseComponent τ bs i j x`: the function `f_{ij}(x)` on `F`.

## Main results

* `ContinuousAlternatingMap.apply_vecCons_prod_eq_sum`: the same splitting for a single
  continuous alternating two-form on a product `EB × EF` of normed spaces.
* `TauCeti.RoughForm.eq_verticalForm_add_sum`: the local form of `τ`.

## Implementation notes

By Tau Ceti's `TauCeti.mpullback_prodMk_verticalForm`, the slices over `x` of the vertical forms
of `σ` and `αᵢ` are `σ(x)` and `αᵢ(x)`, so the components can be recovered from the terms of the
local form. The proof of the local form is linear algebra at each point
(`ContinuousAlternatingMap.apply_vecCons_prod_eq_sum`): the value of `τ` on two vectors is
expanded by bilinearity into the parts along `EB` and along the model space of `F`, the vectors
along `EB` are expanded in the basis `bs`, and the double sum over the indices is folded into a sum
over the pairs `i < j` by `Finset.sum_sum_eq_sum_sum_lt_add_swap`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.3.
-/

public section

noncomputable section

open scoped Manifold

namespace Module.Basis

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {ι : Type*} (bs : Module.Basis ι ℝ EB)

/-- The constant one-form `dxᵢ` on a finite-dimensional real normed space `EB`, for a basis `bs`
of `EB`: its value on a tangent vector `v` is the `i`-th coordinate `bs.coord i v`. -/
def coordOneForm (i : ι) : TauCeti.SmoothForm 𝓘(ℝ, EB) EB ℝ 1 :=
  TauCeti.SmoothForm.const
    (ContinuousAlternatingMap.ofSubsingleton ℝ EB ℝ 0
      (LinearMap.toContinuousLinearMap (bs.coord i)))

/-- The one-form `dxᵢ` takes a tangent vector to its `i`-th coordinate in the basis `bs`. -/
@[simp]
theorem coordOneForm_apply (i : ι) (x : EB) (v : Fin 1 → TangentSpace 𝓘(ℝ, EB) x) :
    (bs.coordOneForm i).val x v = bs.coord i (v 0) := by
  rw [coordOneForm, TauCeti.SmoothForm.const_apply,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, NormedSpace.fromTangentSpace_apply,
    LinearMap.coe_toContinuousLinearMap']

end Module.Basis

namespace ContinuousAlternatingMap

variable {EB EF : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [NormedAddCommGroup EF]
  [NormedSpace ℝ EF] {ι : Type*} [Fintype ι] [LinearOrder ι] (bs : Module.Basis ι ℝ EB)
  (T : (EB × EF) [⋀^Fin 2]→L[ℝ] ℝ)

/-- **A two-form on a product in coordinates along the first factor.** For a basis `bs` of
`EB`, with coordinates `cᵢ = bs.coord i`, a two-form `T` on `EB × EF` takes the value
`T((0, w₁), (0, w₂)) + ∑ᵢ (T((0, w₁), (bsᵢ, 0)) cᵢ(u₂) - T((0, w₂), (bsᵢ, 0)) cᵢ(u₁))
+ ∑_{i<j} T((bsᵢ, 0), (bsⱼ, 0)) (cᵢ(u₁) cⱼ(u₂) - cᵢ(u₂) cⱼ(u₁))` on `(u₁, w₁)` and
`(u₂, w₂)`. -/
theorem apply_vecCons_prod_eq_sum (u₁ u₂ : EB) (w₁ w₂ : EF) :
    T ![(u₁, w₁), (u₂, w₂)] = T ![(0, w₁), (0, w₂)] +
      ∑ i, (T ![(0, w₁), (bs i, 0)] * bs.coord i u₂ - T ![(0, w₂), (bs i, 0)] * bs.coord i u₁) +
      ∑ i, ∑ j with i < j, T ![(bs i, 0), (bs j, 0)] *
        (bs.coord i u₁ * bs.coord j u₂ - bs.coord i u₂ * bs.coord j u₁) := by
  -- Split both vectors into their parts along `EB` and along `EF`.
  have hsplit : T ![(u₁, w₁), (u₂, w₂)] = T ![(u₁, 0), (u₂, 0)] - T ![(0, w₂), (u₁, 0)] +
      T ![(0, w₁), (u₂, 0)] + T ![(0, w₁), (0, w₂)] := by
    rw [show ((u₁, w₁) : EB × EF) = (u₁, 0) + (0, w₁) by simp,
      show ((u₂, w₂) : EB × EF) = (u₂, 0) + (0, w₂) by simp, T.vecCons_add,
      T.apply_vecCons_add_right, T.apply_vecCons_add_right,
      T.apply_vecCons_swap (u₁, 0) (0, w₂)]
    abel
  -- Expand a second vector along `EB` in the basis `bs`.
  have hlin : ∀ (a : EB × EF) (s : Finset ι) (c : ι → ℝ) (v : ι → EB × EF),
      T ![a, ∑ i ∈ s, c i • v i] = ∑ i ∈ s, T ![a, v i] * c i := by
    intro a s c v
    induction s using Finset.cons_induction with
    | empty => simpa using T.apply_vecCons_smul_right 0 a 0
    | cons i s hi ih =>
      rw [Finset.sum_cons, Finset.sum_cons, T.apply_vecCons_add_right,
        T.apply_vecCons_smul_right, ih, smul_eq_mul, mul_comm]
  have hbs : ∀ (a : EB × EF) (u : EB),
      T ![a, (u, 0)] = ∑ i, T ![a, (bs i, 0)] * bs.coord i u := by
    intro a u
    have hu : ((u, 0) : EB × EF) = ∑ i, bs.repr u i • ((bs i, 0) : EB × EF) :=
      Prod.ext (by simp [Prod.fst_sum, bs.sum_repr]) (by simp [Prod.snd_sum])
    rw [hu, hlin]
    simp only [Module.Basis.coord_apply]
  -- The part along `EB` is a two-form on `EB`, expanded in `bs`.
  have hbase : T ![(u₁, 0), (u₂, 0)] = ∑ i, ∑ j with i < j, T ![(bs i, 0), (bs j, 0)] *
      (bs.coord i u₁ * bs.coord j u₂ - bs.coord i u₂ * bs.coord j u₁) := by
    have hfirst : ∀ j, T ![(u₁, 0), (bs j, 0)] =
        ∑ i, T ![(bs i, 0), (bs j, 0)] * bs.coord i u₁ := fun j ↦ by
      rw [T.apply_vecCons_swap, hbs, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [T.apply_vecCons_swap (bs j, 0)]; ring
    rw [hbs]
    simp_rw [hfirst, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine (Finset.sum_sum_eq_sum_sum_lt_add_swap _
      (fun i j ↦ T ![(bs i, 0), (bs j, 0)] * bs.coord i u₁ * bs.coord j u₂) fun i ↦ ?_).trans
      (Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_)
    · have h0 : T ![(bs i, 0), (bs i, 0)] = 0 := T.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl
        Fin.zero_ne_one
      rw [h0, zero_mul, zero_mul]
    · rw [T.apply_vecCons_swap (bs j, 0)]
      ring
  rw [hsplit, hbase, hbs (0, w₁) u₂, hbs (0, w₂) u₁, Finset.sum_sub_distrib]
  ring

end ContinuousAlternatingMap

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
  have hX : Manifold.prodVectorField (I := 𝓘(ℝ, EB)) (J := IF)
      (fun x ↦ (bs i : TangentSpace 𝓘(ℝ, EB) x))
      (0 : (y : F) → TangentSpace IF y) (x, y) = ((bs i, 0) : EB × EF) :=
    Prod.ext (Manifold.prodVectorField_fst _ _ _) (Manifold.prodVectorField_snd _ _ _)
  rw [hX]
  exact (τ (x, y)).apply_vecCons_swap _ _

/-- The **base component** `f_{ij}(x)` of a two-form `τ` on `EB × F`, for the basis `bs` of
`EB`: the function on `F` whose value at `y` is `τ` at `(x, y)` on the fields `(bs i, 0)` and
`(bs j, 0)`. -/
def baseComponent (i j : ι) (x : EB) (y : F) : ℝ :=
  τ (x, y) ![(bs i, 0), (bs j, 0)]

theorem baseComponent_def (i j : ι) (x : EB) (y : F) :
    τ.baseComponent bs i j x y = τ (x, y) ![(bs i, 0), (bs j, 0)] :=
  (rfl)

/-- The base components are antisymmetric in the two indices. -/
theorem baseComponent_swap (i j : ι) (x : EB) (y : F) :
    τ.baseComponent bs j i x y = -τ.baseComponent bs i j x y :=
  ContinuousAlternatingMap.apply_vecCons_swap _ _ _

/-- The pull-back along `Prod.fst` of the one-form `dxᵢ` on `EB` takes a tangent vector of
`EB × F` to the `i`-th coordinate of its component along `EB`. -/
theorem mpullback_fst_coordOneForm_apply [FiniteDimensional ℝ EB] (i : ι) (z : EB × F)
    (v : Fin 1 → TangentSpace (𝓘(ℝ, EB).prod IF) z) :
    mpullback (𝓘(ℝ, EB).prod IF) 𝓘(ℝ, EB) Prod.fst (bs.coordOneForm i).val z v =
      bs.coord i (v 0).1 := by
  rw [mpullback_apply, Module.Basis.coordOneForm_apply, TauCeti.mfderiv_fst_apply]

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
  have h₂ : (fun k ↦ (![v₁, v₂] k).2) = (![v₁.2, v₂.2] : Fin 2 → TangentSpace IF z.2) := by
    funext k; fin_cases k <;> rfl
  have h₁ : ∀ v : TangentSpace (𝓘(ℝ, EB).prod IF) z,
      (fun k ↦ (![v] k).2) = (![v.2] : Fin 1 → TangentSpace IF z.2) := fun v ↦ by
    funext k; fin_cases k; rfl
  simp only [Pi.add_apply, ContinuousAlternatingMap.add_apply, Finset.sum_apply,
    ContinuousAlternatingMap.sum_apply, Pi.smul_apply', ContinuousAlternatingMap.smul_apply,
    mpullback_wedge, wedge_apply_one_one, verticalForm_apply, h₁, h₂,
    mpullback_fst_coordOneForm_apply, baseComponent_def, smul_eq_mul,
    Matrix.cons_val_zero]
  refine ((τ z).apply_vecCons_prod_eq_sum bs v₁.1 v₂.1 v₁.2 v₂.2).trans ?_
  -- The fibre vectors are elements of `EF` on the left and of `TangentSpace IF z.2` on the right,
  -- so the components are matched term by term.
  congr 2
  · exact (τ.fiberComponent_apply z.1 z.2 v₁.2 v₂.2).symm
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact congrArg₂ (· - ·) (congrArg (· * _) (τ.mixedComponent_apply bs i z.1 z.2 v₁.2).symm)
      (congrArg (· * _) (τ.mixedComponent_apply bs i z.1 z.2 v₂.2).symm)

end TauCeti.RoughForm
