/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.Algebra.Module.InnerProducts
public import TauCeti.Geometry.Symplectic.PolarCompatible
import SymplecticGeometry.Analysis.InnerProductSpace.LinearMap

/-!
# The complex structure `J_{g,ω}` of an inner product and a symplectic form

Fix a symplectic form `ω` and an inner product `g` on a space `V` of finite dimension over `ℝ`.
There is exactly one almost complex structure `J` on `V` that preserves `g` and is
compatible with `ω`. This file defines it as `SymplecticGeometry.metricPolarComplexStructure g ω`.
When `A` is the operator with `g (A u) v = ω u v`, it is the polar factor of `A` with respect to
`g`, that is `J = Q⁻¹ A` for the `g`-positive square root `Q` of `-A²`.

The space `V` carries a norm, for the topology of later files, but no inner product of its own:
`g` is any element of `innerProducts V`. When `V` is an inner product space and `g` is its inner
product, the structure is Tau Ceti's `TauCeti.SymplecticForm.polarComplexStructure`.

## Main definitions

* `SymplecticGeometry.metricPolarComplexStructure g ω`: the unique `g`-orthogonal complex
  structure compatible with `ω`.

## Main results

* `TauCeti.SymplecticForm.polarComplexStructure_eq_iff`: on an inner product space, Tau Ceti's
  polar complex structure of `ω` is the only orthogonal complex structure compatible with `ω`.
* `SymplecticGeometry.metricPolarComplexStructure_eq_iff`: the characterization of
  `metricPolarComplexStructure g ω`.
* `SymplecticGeometry.metricPolarComplexStructure_eq_inverse_mul`: the formula `J = Q⁻¹ A`.
* `SymplecticGeometry.exists_operator_and_sqrt_neg_mul_self`: the operators `A` and `Q` of that
  formula exist for every `g` and `ω`.
* `SymplecticGeometry.metricPolarComplexStructure_associatedBilinForm`: for a compatible `J`, the
  construction applied to the metric `ω(·, J ·)` gives back `J`.
* `SymplecticGeometry.metricPolarComplexStructure_transport`: naturality under linear
  isomorphisms.
* `SymplecticGeometry.metricPolarComplexStructure_innerSL`: comparison with Tau Ceti's
  construction for the inner product of an inner product space.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.5.6
-/

public section

open scoped RealInnerProductSpace

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- When `V` is an inner product space over `ℝ` of finite dimension, the polar complex structure
of a symplectic form `ω` is the only almost complex structure that is orthogonal and compatible
with `ω`. -/
theorem polarComplexStructure_eq_iff :
    ω.polarComplexStructure = J ↔ (∀ u v, ⟪J u, J v⟫ = ⟪u, v⟫) ∧ ω.Compatible J := by
  refine ⟨?_, fun ⟨hJ, hc⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨ω.inner_polarComplexStructure_apply_apply, ω.compatible_polarComplexStructure⟩
  -- `Q = -J A` is positive, and `A = J Q`, so `J` is the isometric polar factor of `A`.
  have hskew : ∀ u v, ⟪J u, v⟫ = -⟪u, J v⟫ :=
    J.bilinForm_apply_left_eq_neg_apply_right (g := innerₗ V) hJ
  have hQ : ∀ u v, ⟪-J (ω.innerOperator u), v⟫ = ω u (J v) := fun u v ↦ by
    rw [inner_neg_left, hskew, neg_neg, inner_innerOperator_apply]
  have hpos : (-(J.toLinearMap ∘ₗ ω.innerOperator)).IsPositive := by
    refine ⟨fun u v ↦ ?_, fun u ↦ ?_⟩
    · simp only [LinearMap.neg_apply, LinearMap.comp_apply]
      rw [hQ, real_inner_comm, hQ, hc.associatedBilinForm_apply_swap]
    · simp only [LinearMap.neg_apply, LinearMap.comp_apply, RCLike.re_to_real, hQ]
      rcases eq_or_ne u 0 with rfl | hu
      · simp
      · exact (hc.tames u hu).le
  have h := LinearMap.eq_polarIsometry_of_comp_eq ω.innerOperator_injective hpos
    (J.toLinearMap.isometryOfInner hJ) (by ext u; simp)
  refine AlmostComplexStructure.toLinearMap_injective ?_
  rw [polarComplexStructure_toLinearMap, ← LinearMap.polarIsometry_toLinearMap _
    ω.innerOperator_injective, ← h, LinearMap.isometryOfInner_toLinearMap]

end TauCeti.SymplecticForm

namespace SymplecticGeometry

open TauCeti Module

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {g : innerProducts V} {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- There is exactly one almost complex structure that preserves the inner product `g` and is
compatible with the symplectic form `ω`. -/
theorem existsUnique_metricPolarComplexStructure (g : innerProducts V) (ω : SymplecticForm V) :
    ∃! J : AlmostComplexStructure V,
      (∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (J u) (J v) = (g : V →L[ℝ] V →L[ℝ] ℝ) u v) ∧
        ω.Compatible J := by
  obtain ⟨e, he⟩ := innerProducts.exists_transport_eq_innerSL g
  -- After transport along `e`, the conditions characterize Tau Ceti's polar structure.
  have key : ∀ J : AlmostComplexStructure V,
      ((∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (J u) (J v) = (g : V →L[ℝ] V →L[ℝ] ℝ) u v) ∧
        ω.Compatible J) ↔
        (ω.transport e.toLinearEquiv).polarComplexStructure = J.transport e.toLinearEquiv :=
      fun J ↦ by
    rw [← and_congr (innerProducts.forall_transport_apply_transport_iff e g J)
      (ω.compatible_transport_iff J e.toLinearEquiv), he,
      SymplecticForm.polarComplexStructure_eq_iff]
    simp only [innerSL_real_apply_apply]
  refine ⟨(ω.transport e.toLinearEquiv).polarComplexStructure.transport e.toLinearEquiv.symm,
    (key _).2 ?_, fun J hJ ↦ ?_⟩
  · rw [AlmostComplexStructure.transport_trans, LinearEquiv.symm_trans_self,
      AlmostComplexStructure.transport_refl]
  · rw [(key J).1 hJ, AlmostComplexStructure.transport_trans, LinearEquiv.self_trans_symm,
      AlmostComplexStructure.transport_refl]

/-- The almost complex structure `J_{g,ω}` of an inner product `g` and a symplectic form `ω`: the
unique complex structure that preserves `g` and is compatible with `ω`
(`SymplecticGeometry.metricPolarComplexStructure_eq_iff`). It is the polar factor, for `g`, of
the operator `A` with `g (A u) v = ω u v`
(`SymplecticGeometry.metricPolarComplexStructure_eq_inverse_mul`). -/
noncomputable def metricPolarComplexStructure (g : innerProducts V) (ω : SymplecticForm V) :
    AlmostComplexStructure V :=
  (existsUnique_metricPolarComplexStructure g ω).exists.choose

/-- `J_{g,ω}` is the only almost complex structure that preserves `g` and is compatible with
`ω`. -/
theorem metricPolarComplexStructure_eq_iff :
    metricPolarComplexStructure g ω = J ↔
      (∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (J u) (J v) = (g : V →L[ℝ] V →L[ℝ] ℝ) u v) ∧
        ω.Compatible J := by
  have hspec := (existsUnique_metricPolarComplexStructure g ω).exists.choose_spec
  refine ⟨?_, fun h ↦ (existsUnique_metricPolarComplexStructure g ω).unique hspec h⟩
  rintro rfl
  exact hspec

variable (g ω)

/-- `J_{g,ω}` is compatible with `ω`. -/
theorem compatible_metricPolarComplexStructure :
    ω.Compatible (metricPolarComplexStructure g ω) :=
  (metricPolarComplexStructure_eq_iff.1 rfl).2

/-- `J_{g,ω}` is orthogonal for `g`. -/
@[simp]
theorem apply_metricPolarComplexStructure_apply (u v : V) :
    (g : V →L[ℝ] V →L[ℝ] ℝ) (metricPolarComplexStructure g ω u)
      (metricPolarComplexStructure g ω v) = (g : V →L[ℝ] V →L[ℝ] ℝ) u v :=
  (metricPolarComplexStructure_eq_iff.1 rfl).1 u v

/-- `J_{g,ω}` is skew-adjoint for `g`. -/
theorem apply_metricPolarComplexStructure_left (u v : V) :
    (g : V →L[ℝ] V →L[ℝ] ℝ) (metricPolarComplexStructure g ω u) v =
      -(g : V →L[ℝ] V →L[ℝ] ℝ) u (metricPolarComplexStructure g ω v) :=
  (metricPolarComplexStructure g ω).bilinForm_apply_left_eq_neg_apply_right
    (g := (g : V →L[ℝ] V →L[ℝ] ℝ).toBilinForm) (apply_metricPolarComplexStructure_apply g ω) u v

/-- **Naturality of `J_{g,ω}`.** Pushing `g` and `ω` forward along a linear isomorphism `e` pushes
`J_{g,ω}` forward along `e`. In particular `J_{g,ω}` is equivariant under the general linear
group. -/
theorem metricPolarComplexStructure_transport (e : V ≃L[ℝ] W) :
    metricPolarComplexStructure (innerProducts.transport e g) (ω.transport e.toLinearEquiv) =
      (metricPolarComplexStructure g ω).transport e.toLinearEquiv :=
  metricPolarComplexStructure_eq_iff.2 <|
    (and_congr (innerProducts.forall_transport_apply_transport_iff e g _)
      (ω.compatible_transport_iff _ e.toLinearEquiv)).2
      (metricPolarComplexStructure_eq_iff.1 rfl)

/-- For the inner product of an inner product space, `J_{g,ω}` is Tau Ceti's polar complex
structure of `ω`. -/
theorem metricPolarComplexStructure_innerSL {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ω : SymplecticForm E) :
    metricPolarComplexStructure ⟨innerSL ℝ, innerSL_mem_innerProducts⟩ ω =
      ω.polarComplexStructure :=
  metricPolarComplexStructure_eq_iff.2
    ⟨fun u v ↦ by
      simpa only [innerSL_real_apply_apply] using ω.inner_polarComplexStructure_apply_apply u v,
    ω.compatible_polarComplexStructure⟩

variable {g ω}

/-- A compatible complex structure `J` is `J_{g,ω}` for its own metric `g = ω(·, J ·)`. -/
theorem metricPolarComplexStructure_associatedBilinForm (h : ω.Compatible J) :
    metricPolarComplexStructure ⟨_, h.associatedBilinForm_mem_innerProducts⟩ ω = J :=
  metricPolarComplexStructure_eq_iff.2 ⟨fun u v ↦ by
    have := h.invariant.apply_add_apply_eq_zero u v
    simp only [LinearMap.toContinuousBilinearMap_apply, SymplecticForm.associatedBilinForm_apply,
      AlmostComplexStructure.apply_apply, map_neg]
    beta_reduce at this ⊢
    linarith, h⟩

/-- `J_{g,ω}` commutes with the operator `A` of `ω` with respect to `g`, defined by
`g (A u) v = ω u v`. -/
theorem commute_metricPolarComplexStructure {A : V →L[ℝ] V}
    (hA : ∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (A u) v = ω u v) :
    Commute (LinearMap.toContinuousLinearMap (metricPolarComplexStructure g ω).toLinearMap) A := by
  set J := metricPolarComplexStructure g ω
  refine ContinuousLinearMap.ext fun u ↦ innerProducts.ext_apply_right g fun v ↦ ?_
  -- `J` is skew for `g`, and skew for `ω` since `ω` is `J`-invariant.
  have hω := (compatible_metricPolarComplexStructure g ω).invariant.apply_add_apply_eq_zero u v
  simp only [mul_apply_eq_comp, LinearMap.coe_toContinuousLinearMap']
  rw [apply_metricPolarComplexStructure_left, hA, hA]
  beta_reduce at hω ⊢
  linarith

/-- If `Q` is a square root of `-A²` that is self-adjoint and positive definite for `g`, where
`g (A u) v = ω u v`, then `J_{g,ω} Q = A`: this is the polar decomposition of `A` for `g`. The
proof carries `g` to the standard inner product of a Euclidean space, where `Q` becomes the
modulus of the operator of the transported form. -/
private theorem metricPolarComplexStructure_apply_of_mul_self_eq {A Q : V →L[ℝ] V}
    (hA : ∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (A u) v = ω u v)
    (hQs : ∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (Q u) v = (g : V →L[ℝ] V →L[ℝ] ℝ) u (Q v))
    (hQp : ∀ v, v ≠ 0 → 0 < (g : V →L[ℝ] V →L[ℝ] ℝ) (Q v) v)
    (hQ : Q * Q = -(A * A)) (x : V) :
    metricPolarComplexStructure g ω (Q x) = A x := by
  obtain ⟨e, he⟩ := innerProducts.exists_transport_eq_innerSL g
  have he' := (innerProducts.transport_eq_innerSL_iff e g).1 he
  set ω' := ω.transport e.toLinearEquiv with hω'
  have hJ : ω'.polarComplexStructure =
      (metricPolarComplexStructure g ω).transport e.toLinearEquiv := by
    rw [← metricPolarComplexStructure_transport, he, metricPolarComplexStructure_innerSL]
  have hA' : e.toLinearEquiv.conj (A : V →ₗ[ℝ] V) = ω'.innerOperator := by
    refine ω'.eq_innerOperator_iff.2 fun u v ↦ ?_
    obtain ⟨y, rfl⟩ := e.surjective u
    obtain ⟨z, rfl⟩ := e.surjective v
    simp [hω', he', hA]
  have hQ' : e.toLinearEquiv.conj (Q : V →ₗ[ℝ] V) = ω'.innerOperator.operatorAbs := by
    refine LinearMap.IsPositive.eq_operatorAbs ⟨fun u v ↦ ?_, fun u ↦ ?_⟩ ?_
    · obtain ⟨y, rfl⟩ := e.surjective u
      obtain ⟨z, rfl⟩ := e.surjective v
      simp [he', hQs]
    · obtain ⟨y, rfl⟩ := e.surjective u
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      · simpa [he'] using (hQp y hy).le
    · rw [SymplecticForm.adjoint_innerOperator, ← hA']
      refine LinearMap.ext fun u ↦ ?_
      obtain ⟨y, rfl⟩ := e.surjective u
      simpa using congr(e ($hQ y))
  have := ω'.polarComplexStructure_apply_operatorAbs (e x)
  rw [← hQ', ← hA', hJ] at this
  simpa using this

/-- **The formula for `J_{g,ω}`.** Let `A` be the operator of `ω` with respect to `g`, so that
`g (A u) v = ω u v`, and let `Q` be the square root of `-A²` that is self-adjoint and positive
definite for `g`. Then `J_{g,ω} = Q⁻¹ A`. -/
theorem metricPolarComplexStructure_eq_inverse_mul {A Q : V →L[ℝ] V}
    (hA : ∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (A u) v = ω u v)
    (hQs : ∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (Q u) v = (g : V →L[ℝ] V →L[ℝ] ℝ) u (Q v))
    (hQp : ∀ v, v ≠ 0 → 0 < (g : V →L[ℝ] V →L[ℝ] ℝ) (Q v) v)
    (hQ : Q * Q = -(A * A)) :
    LinearMap.toContinuousLinearMap (metricPolarComplexStructure g ω).toLinearMap =
      Ring.inverse Q * A := by
  set J := metricPolarComplexStructure g ω
  have hJQ := metricPolarComplexStructure_apply_of_mul_self_eq hA hQs hQp hQ
  have hcomm (x : V) : A (J x) = J (A x) :=
    (congr($((commute_metricPolarComplexStructure hA).eq) x)).symm
  -- `Q = -J A`, so `Q` commutes with `J`, and `A = Q J`.
  have hQJ (x : V) : Q (J x) = A x := by
    have hQx (y : V) : Q y = -J (A y) := by rw [← hJQ, J.apply_apply, neg_neg]
    rw [hQx, hcomm, J.apply_apply, neg_neg]
  have hinj : Function.Injective Q := (injective_iff_map_eq_zero Q).2 fun x hx ↦ by
    by_contra hne
    simpa [hx] using hQp x hne
  have hu : IsUnit Q := ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.2 <|
    (LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.2 hinj)
  have hAQ : A = Q * LinearMap.toContinuousLinearMap J.toLinearMap :=
    ContinuousLinearMap.ext fun x ↦ by simp [hQJ]
  rw [hAQ, Ring.inverse_mul_cancel_left _ _ hu]

variable (g ω) in
/-- For every inner product `g` and symplectic form `ω`, there are an operator `A` with
`g (A u) v = ω u v` and a square root `Q` of `-A²` that is self-adjoint and positive definite
for `g`: the data of `SymplecticGeometry.metricPolarComplexStructure_eq_inverse_mul`. -/
theorem exists_operator_and_sqrt_neg_mul_self :
    ∃ A Q : V →L[ℝ] V, (∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (A u) v = ω u v) ∧
      (∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (Q u) v = (g : V →L[ℝ] V →L[ℝ] ℝ) u (Q v)) ∧
      (∀ v, v ≠ 0 → 0 < (g : V →L[ℝ] V →L[ℝ] ℝ) (Q v) v) ∧ Q * Q = -(A * A) := by
  -- Carry `g` to the standard inner product, and pull back the operator of the transported form
  -- and its modulus.
  obtain ⟨e, he⟩ := innerProducts.exists_transport_eq_innerSL g
  have he' := (innerProducts.transport_eq_innerSL_iff e g).1 he
  set ω' := ω.transport e.toLinearEquiv with hω'
  set A' := ω'.innerOperator
  have hQ'p := A'.isPositive_operatorAbs
  refine ⟨e.symm.toContinuousLinearMap ∘L LinearMap.toContinuousLinearMap A' ∘L
      e.toContinuousLinearMap,
    e.symm.toContinuousLinearMap ∘L LinearMap.toContinuousLinearMap A'.operatorAbs ∘L
      e.toContinuousLinearMap, fun u v ↦ ?_, fun u v ↦ ?_, fun v hv ↦ ?_, ?_⟩
  · rw [← he']
    simp [hω', A', SymplecticForm.inner_innerOperator_apply]
  · rw [← he', ← he']
    simpa using hQ'p.isSymmetric (e u) (e v)
  · rw [← he']
    simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      LinearMap.coe_toContinuousLinearMap', Function.comp_apply,
      ContinuousLinearEquiv.apply_symm_apply]
    rw [← SymplecticForm.apply_polarComplexStructure]
    exact (SymplecticForm.compatible_polarComplexStructure ω').tames _
      ((map_ne_zero_iff _ e.injective).2 hv)
  · have h := LinearMap.operatorAbs_mul_self_of_adjoint_eq_neg ω'.adjoint_innerOperator
    ext x
    simpa using congr(e.symm ($h (e x)))

end SymplecticGeometry

end
