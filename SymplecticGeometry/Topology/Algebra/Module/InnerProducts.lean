/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Basic
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Geometry.Symplectic.Transport
public import TauCeti.Topology.Algebra.Module.BilinearForm
public import TauCeti.Topology.Algebra.Module.SymmetricBilinear.Basic
import SymplecticGeometry.Analysis.InnerProductSpace.LinearMap
import SymplecticGeometry.Topology.Algebra.Module.BilinearForm

/-!
# The space of inner products

The inner products on a real normed space `V` are the continuous bilinear forms
`g : V →L[ℝ] V →L[ℝ] ℝ` that are symmetric and positive on nonzero vectors. They form the subset
`innerProducts V` of the continuous bilinear forms, with the topology of the operator norm. It is
convex, hence contractible as soon as it is nonempty, and it is nonempty when `V` is
finite-dimensional. A continuous linear equivalence `e : V ≃L[ℝ] W` pushes inner products
forward, `g ↦ g (e.symm ·) (e.symm ·)`, which is a homeomorphism.

## Main definitions

* `SymplecticGeometry.innerProducts V`: the symmetric continuous bilinear forms on `V` that are
  positive on nonzero vectors.
* `SymplecticGeometry.innerProducts.transport e`: the homeomorphism
  `innerProducts V ≃ₜ innerProducts W` induced by `e : V ≃L[ℝ] W`.

## Main results

* `SymplecticGeometry.symmetrizeBilinear_mem_innerProducts`: the symmetric part of a form that
  is positive on nonzero vectors is an inner product.
* `InnerProductSpace.isStrictlyPositive_continuousLinearMapOfBilin_symmetrizeBilinear`: the
  Riesz map of the symmetric part of a form that is positive on nonzero vectors is strictly
  positive.
* `SymplecticGeometry.convex_innerProducts`: the inner products form a convex set.
* `SymplecticGeometry.innerProducts_eq_inter`: they are the symmetric forms that are positive
  on nonzero vectors; in finite dimensions the second condition is open
  (`TauCeti.isOpen_setOf_forall_bilinear_apply_self_pos`).
* The instances `Nonempty` and `ContractibleSpace` for `innerProducts V`, when `V` is
  finite-dimensional.
* `SymplecticGeometry.innerProducts.transport_eq_innerSL_iff`: the transport of `g` along `e` is
  the standard inner product exactly when `e` carries `g` to it.
* `SymplecticGeometry.innerProducts.exists_transport_eq_innerSL`: every inner product on a
  finite-dimensional space is carried to the standard one of a Euclidean space by some linear
  isomorphism.
* `SymplecticGeometry.innerSL_mem_innerProducts`: the inner product of an inner product space.
* `TauCeti.SymplecticForm.Compatible.associatedBilinForm_mem_innerProducts`: the form
  `ω(·, J ·)` of a compatible pair.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.5
-/

public section

open Module

namespace SymplecticGeometry

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The inner products on a real normed space `V`: the continuous bilinear forms on `V` that are
symmetric and positive on every nonzero vector. -/
def innerProducts : Set (V →L[ℝ] V →L[ℝ] ℝ) :=
  {g | (∀ v w, g v w = g w v) ∧ ∀ v, v ≠ 0 → 0 < g v v}

variable {V}

@[simp]
theorem mem_innerProducts {g : V →L[ℝ] V →L[ℝ] ℝ} :
    g ∈ innerProducts V ↔ (∀ v w, g v w = g w v) ∧ ∀ v, v ≠ 0 → 0 < g v v :=
  Iff.rfl

/-- The symmetric part `½ (g + gᵀ)` of a continuous bilinear form `g` that is positive on nonzero
vectors is an inner product. -/
theorem symmetrizeBilinear_mem_innerProducts {g : V →L[ℝ] V →L[ℝ] ℝ}
    (hg : ∀ v, v ≠ 0 → 0 < g v v) :
    (ContinuousLinearMap.symmetrizeBilinear g).val ∈ innerProducts V :=
  ⟨fun u v ↦ by simp [ContinuousLinearMap.symmetrizeBilinear_apply, add_comm], fun v hv ↦ by
    simpa [ContinuousLinearMap.symmetrizeBilinear_apply] using hg v hv⟩

/-- The Riesz map of the symmetric part of a continuous bilinear form that is positive on nonzero
vectors is strictly positive. -/
theorem _root_.InnerProductSpace.isStrictlyPositive_continuousLinearMapOfBilin_symmetrizeBilinear
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {g : W →L[ℝ] W →L[ℝ] ℝ} (hg : ∀ v, v ≠ 0 → 0 < g v v) :
    IsStrictlyPositive (InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ)
      (ContinuousLinearMap.symmetrizeBilinear g).val) :=
  InnerProductSpace.isStrictlyPositive_continuousLinearMapOfBilin_iff.2
    ⟨(TauCeti.mem_symmetricBilinearMaps ℝ W ℝ _).1
      (ContinuousLinearMap.symmetrizeBilinear g).property, fun v hv ↦ by simpa using hg v hv⟩

variable (V) in
/-- The inner products form a convex set. -/
theorem convex_innerProducts : Convex ℝ (innerProducts V) :=
  TauCeti.convex_setOfPred_symm_pos

variable (V) in
/-- The inner products are the symmetric forms that are positive on nonzero vectors. The
symmetric forms are a closed subspace, and in finite dimensions positivity on nonzero vectors
is open (`TauCeti.isOpen_setOf_forall_bilinear_apply_self_pos`), so the inner products are open
in the symmetric forms. -/
theorem innerProducts_eq_inter :
    innerProducts V =
      {g : V →L[ℝ] V →L[ℝ] ℝ | ∀ v w, g v w = g w v} ∩ {g | ∀ v, v ≠ 0 → 0 < g v v} :=
  (rfl)

/-- The inner product of a real inner product space, as a continuous bilinear form, is an inner
product. -/
theorem innerSL_mem_innerProducts {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    innerSL ℝ ∈ innerProducts E :=
  ⟨fun v w ↦ real_inner_comm w v, fun _ hv ↦ real_inner_self_pos.2 hv⟩

namespace innerProducts

variable {W X : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup X]
  [NormedSpace ℝ X]

/-- Pulling an inner product back along an injective continuous linear map `f : W →L[ℝ] V`,
`g ↦ g (f ·) (f ·)`, gives an inner product. In particular an inner product restricts to one on
every subspace. -/
theorem bilinearComp_mem {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : g ∈ innerProducts V) (f : W →L[ℝ] V)
    (hf : Function.Injective f) : g.bilinearComp f f ∈ innerProducts W :=
  ⟨fun v w ↦ by simp [hg.1 (f v)], fun v hv ↦ by
    simpa using hg.2 (f v) (by simpa [map_eq_zero_iff _ hf] using hv)⟩

/-- The homeomorphism of the inner products on `V` with those on `W` induced by a continuous
linear equivalence `e : V ≃L[ℝ] W`: it pushes an inner product forward along `e`, sending `g` to
`(w, w') ↦ g (e.symm w) (e.symm w')`. -/
noncomputable def transport (e : V ≃L[ℝ] W) : innerProducts V ≃ₜ innerProducts W where
  toFun g := ⟨e.bilinearCongr g.val, (e.bilinearCongr_apply_eq_bilinearComp g.val).symm ▸
    bilinearComp_mem g.property _ e.symm.injective⟩
  invFun g := ⟨e.symm.bilinearCongr g.val, (e.symm.bilinearCongr_apply_eq_bilinearComp g.val).symm ▸
    bilinearComp_mem g.property _ e.injective⟩
  left_inv g := by ext; simp
  right_inv g := by ext; simp
  continuous_toFun := (e.bilinearCongr (G := ℝ)).continuous.comp continuous_subtypeVal
    |>.subtype_mk _
  continuous_invFun := (e.symm.bilinearCongr (G := ℝ)).continuous.comp continuous_subtypeVal
    |>.subtype_mk _

@[simp]
theorem transport_apply (e : V ≃L[ℝ] W) (g : innerProducts V) (w w' : W) :
    (transport e g : W →L[ℝ] W →L[ℝ] ℝ) w w' = (g : V →L[ℝ] V →L[ℝ] ℝ) (e.symm w) (e.symm w') :=
  e.bilinearCongr_apply _ _ _

@[simp]
theorem transport_symm (e : V ≃L[ℝ] W) : (transport e).symm = transport e.symm :=
  (rfl)

@[simp]
theorem transport_trans (e₁ : V ≃L[ℝ] W) (e₂ : W ≃L[ℝ] X) :
    (transport e₁).trans (transport e₂) = transport (e₁.trans e₂) := by
  ext g w w'
  simp

@[simp]
theorem transport_refl : transport (ContinuousLinearEquiv.refl ℝ V) = Homeomorph.refl _ := by
  ext g w w'
  simp

/-- An inner product separates points through its first argument. -/
theorem ext_apply_right (g : innerProducts V) {x y : V}
    (h : ∀ v, (g : V →L[ℝ] V →L[ℝ] ℝ) x v = (g : V →L[ℝ] V →L[ℝ] ℝ) y v) : x = y := by
  by_contra hxy
  have hpos := g.property.2 (x - y) (sub_ne_zero.2 hxy)
  simp [h] at hpos

/-- An almost complex structure `J` preserves `g` exactly when its transport along `e` preserves
the transport of `g`. -/
theorem forall_transport_apply_transport_iff (e : V ≃L[ℝ] W) (g : innerProducts V)
    (J : TauCeti.AlmostComplexStructure V) :
    (∀ u v, (transport e g : W →L[ℝ] W →L[ℝ] ℝ)
        (J.transport e.toLinearEquiv u) (J.transport e.toLinearEquiv v) =
        (transport e g : W →L[ℝ] W →L[ℝ] ℝ) u v) ↔
      ∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (J u) (J v) = (g : V →L[ℝ] V →L[ℝ] ℝ) u v :=
  ⟨fun h u v ↦ by simpa using h (e u) (e v), fun h u v ↦ by simpa using h (e.symm u) (e.symm v)⟩

/-- The transport of `g` along `e : V ≃L[ℝ] E` is the inner product of the inner product space
`E` exactly when `e` carries `g` to that inner product: `⟪e u, e v⟫ = g u v`. -/
theorem transport_eq_innerSL_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : V ≃L[ℝ] E) (g : innerProducts V) :
    transport e g = ⟨innerSL ℝ, innerSL_mem_innerProducts⟩ ↔
      ∀ u v, inner ℝ (e u) (e v) = (g : V →L[ℝ] V →L[ℝ] ℝ) u v := by
  refine ⟨fun he u v ↦ ?_, fun h ↦ Subtype.ext ?_⟩
  · have := congrArg (fun h : innerProducts _ ↦ (h : _ →L[ℝ] _ →L[ℝ] ℝ) (e u) (e v)) he
    simp only [transport_apply, ContinuousLinearEquiv.symm_apply_apply,
      innerSL_real_apply_apply] at this
    exact this.symm
  · ext w w'
    simp only [transport_apply, ← h, ContinuousLinearEquiv.apply_symm_apply,
      innerSL_real_apply_apply]

end innerProducts

variable [FiniteDimensional ℝ V]

/-- Every inner product on a finite-dimensional real normed space `V` is the pull-back of the
standard inner product of a Euclidean space of the same dimension along some continuous linear
isomorphism. -/
theorem innerProducts.exists_transport_eq_innerSL (g : innerProducts V) :
    ∃ e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V)),
      transport e g = ⟨innerSL ℝ, innerSL_mem_innerProducts⟩ := by
  let E := EuclideanSpace ℝ (Fin (finrank ℝ V))
  let e₀ : V ≃L[ℝ] E := .ofFinrankEq finrank_euclideanSpace_fin.symm
  let h : E →L[ℝ] E →L[ℝ] ℝ := transport e₀ g
  have hH := InnerProductSpace.isStrictlyPositive_continuousLinearMapOfBilin_iff.2
    (transport e₀ g).property
  refine ⟨e₀.trans (h.metricChangeEquiv hH).symm, Subtype.ext ?_⟩
  ext w w'
  rw [innerSL_real_apply_apply, ← h.apply_metricChangeTransport_metricChangeTransport hH w w']
  simp [h]

variable (V) in
/-- A finite-dimensional real normed space has an inner product: pull back the inner product of
a Euclidean space of the same dimension. -/
theorem innerProducts_nonempty : (innerProducts V).Nonempty := by
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V)) := .ofFinrankEq (by simp)
  exact ⟨_, innerProducts.bilinearComp_mem innerSL_mem_innerProducts
    (e : V →L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V))) e.injective⟩

instance : Nonempty (innerProducts V) :=
  (innerProducts_nonempty V).to_subtype

/-- The space of inner products on a finite-dimensional real normed space is contractible. -/
instance : ContractibleSpace (innerProducts V) :=
  (convex_innerProducts V).contractibleSpace (innerProducts_nonempty V)

end SymplecticGeometry

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The form `ω(·, J ·)` of a compatible pair `(ω, J)`, as a continuous bilinear form, is an inner
product. -/
theorem Compatible.associatedBilinForm_mem_innerProducts {ω : SymplecticForm V}
    {J : AlmostComplexStructure V} (h : ω.Compatible J) :
    (ω.associatedBilinForm J).toContinuousBilinearMap ∈ SymplecticGeometry.innerProducts V :=
  ⟨fun v w ↦ by simpa using h.associatedBilinForm_isSymm.eq v w, fun v hv ↦ by
    simpa using h.tames v hv⟩

end TauCeti.SymplecticForm

end
