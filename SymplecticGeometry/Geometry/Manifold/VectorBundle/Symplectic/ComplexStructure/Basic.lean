/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ComplexStructure
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section

/-!
# Tame and compatible pairs on a vector bundle

Let `ω` be a two-form and `J` a complex structure on a real vector bundle `V → M`, of possibly
different regularities. This file defines when `ω` tames `J` (`ω(v, J v) > 0` for every nonzero
`v`), when `ω` is `J`-invariant (`ω(J v, J w) = ω(v, w)`), and when the pair is compatible (both).
These follow Tau Ceti's `TauCeti.SmoothTwoForm.Tames`, `Invariant` and `Compatible` for the
tangent bundle, and on each fibre they are Tau Ceti's linear `TauCeti.SymplecticForm.Tames` and
`TauCeti.SymplecticForm.Compatible`.

## Main definitions

* `SymplecticGeometry.Bundle.ContMDiffTwoForm.Tames`, `Invariant` and `Compatible`.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.compatibleForm g J`: for a bundle metric
  `g` and a complex structure `J`, the two-form `ω_{g,J}(u, v) = (g(J u, v) - g(u, J v)) / 2`.
  With this sign, the formula for the Euclidean inner product and the standard complex structure
  `J₀` of `StdSpace ι` gives the standard form `stdForm ι`, since `J₀` is skew-adjoint and
  `stdForm ι z w = ⟪J₀ z, w⟫` (`SymplecticGeometry.stdForm_apply_eq_inner`).

## Main results

* `Tames.isNondegenerate`, `Compatible.isNondegenerate`: a form taming some complex structure is
  nondegenerate.
* `IsNondegenerate.tames_iff`, `IsNondegenerate.invariant_iff`, `IsNondegenerate.compatible_iff`:
  for a nondegenerate form, the predicates are Tau Ceti's linear ones on every fibre.
* `Tames.pushforward`, `Invariant.pushforward`, `Compatible.pushforward`: transport along an
  isomorphism of bundles, moving the form and the complex structure together.
* `tames_tangentEquiv_iff`, `invariant_tangentEquiv_iff`, `compatible_tangentEquiv_iff`: on the
  tangent bundle, the predicates are Tau Ceti's.
* `convex_setOf_tames`, `convex_setOf_compatible`: the two-forms taming, or compatible with, a
  fixed complex structure form a convex set.
* `ContMDiffComplexStructure.compatible_compatibleForm`: `ω_{g,J}` is compatible with `J`.

## Implementation notes

The smoothness of `ω_{g,J}` comes from Tau Ceti's
`TauCeti.contMDiffAt_continuousAlternatingMap_bundle_of_bilinear`, applied to the bilinear section
`(g ∘ J - (g ∘ J)ᵀ) / 2`, whose transpose is Tau Ceti's `TauCeti.Manifold.transposeBilinearSection`.
That lemma reads a two-form through its values on a basis of the model fibre, so `compatibleForm`
assumes that `F` is finite-dimensional.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.5, §2.6
-/

public section

noncomputable section

open _root_.Bundle Set
open scoped Manifold

namespace SymplecticGeometry.Bundle

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n m : ℕ∞}

namespace ContMDiffTwoForm

/-! ### Tameness, invariance and compatibility -/

/-- A two-form `ω` tames a complex structure `J` when `ω(v, J v) > 0` for every nonzero vector `v`
of every fibre. -/
def Tames (ω : ContMDiffTwoForm I n F V) (J : ContMDiffComplexStructure I m F V) : Prop :=
  ∀ (x : M) (v : V x), v ≠ 0 → 0 < ω.bilinFormAt x v (J x v)

/-- A two-form `ω` is invariant under a complex structure `J` when `ω(J v, J w) = ω(v, w)` for all
vectors `v`, `w` of every fibre. -/
def Invariant (ω : ContMDiffTwoForm I n F V) (J : ContMDiffComplexStructure I m F V) : Prop :=
  ∀ (x : M) (v w : V x), ω.bilinFormAt x (J x v) (J x w) = ω.bilinFormAt x v w

/-- A two-form is compatible with a complex structure when it is invariant under it and tames
it. -/
structure Compatible (ω : ContMDiffTwoForm I n F V) (J : ContMDiffComplexStructure I m F V) :
    Prop where
  /-- The form is invariant under the complex structure. -/
  invariant : ω.Invariant J
  /-- The form tames the complex structure. -/
  tames : ω.Tames J

section Predicates

variable {ω : ContMDiffTwoForm I n F V} {J : ContMDiffComplexStructure I m F V}

/-- Tameness is positivity of `ω_x(v, J v)` on every nonzero vector. -/
theorem tames_iff : ω.Tames J ↔ ∀ (x : M) (v : V x), v ≠ 0 → 0 < ω x ![v, J x v] := by
  simp only [Tames, bilinFormAt_apply]

/-- Invariance is the identity `ω_x(J v, J w) = ω_x(v, w)` on every fibre. -/
theorem invariant_iff :
    ω.Invariant J ↔ ∀ (x : M) (v w : V x), ω x ![J x v, J x w] = ω x ![v, w] := by
  simp only [Invariant, bilinFormAt_apply]

/-- Compatibility is invariance together with tameness. -/
theorem compatible_iff : ω.Compatible J ↔ ω.Invariant J ∧ ω.Tames J :=
  ⟨fun h ↦ ⟨h.invariant, h.tames⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- An invariant form takes the same value on `(J v, J w)` as on `(v, w)`. -/
theorem Invariant.apply (h : ω.Invariant J) (x : M) (v w : V x) :
    ω x ![J x v, J x w] = ω x ![v, w] :=
  invariant_iff.1 h x v w

/-- A form that tames a complex structure is positive on `(v, J v)` for every nonzero `v`. -/
theorem Tames.apply_pos (h : ω.Tames J) {x : M} {v : V x} (hv : v ≠ 0) :
    0 < ω x ![v, J x v] :=
  tames_iff.1 h x v hv

/-- A form that tames some complex structure is nondegenerate. -/
theorem Tames.isNondegenerate (h : ω.Tames J) : ω.IsNondegenerate := by
  rw [isNondegenerate_iff_separatingLeft]
  intro x v hv
  by_contra hv0
  exact (h.apply_pos hv0).ne' (hv (J x v))

/-- A form compatible with some complex structure is nondegenerate. -/
theorem Compatible.isNondegenerate (h : ω.Compatible J) : ω.IsNondegenerate :=
  h.tames.isNondegenerate

/-- For a nondegenerate form, tameness is Tau Ceti's linear tameness on every fibre. -/
theorem IsNondegenerate.tames_iff (h : ω.IsNondegenerate) :
    ω.Tames J ↔ ∀ x, (h.symplecticFormAt x).Tames (J.almostComplexStructureAt x) := by
  simp only [Tames, TauCeti.SymplecticForm.Tames, IsNondegenerate.symplecticFormAt_apply,
    ContMDiffComplexStructure.almostComplexStructureAt_apply, bilinFormAt_apply]

/-- For a nondegenerate form, invariance is Tau Ceti's linear invariance on every fibre. -/
theorem IsNondegenerate.invariant_iff (h : ω.IsNondegenerate) :
    ω.Invariant J ↔ ∀ x, (h.symplecticFormAt x).Invariant (J.almostComplexStructureAt x) := by
  simp only [ContMDiffTwoForm.invariant_iff, TauCeti.SymplecticForm.invariant_iff,
    IsNondegenerate.symplecticFormAt_apply,
    ContMDiffComplexStructure.almostComplexStructureAt_apply]

/-- For a nondegenerate form, compatibility is Tau Ceti's linear compatibility on every fibre. -/
theorem IsNondegenerate.compatible_iff (h : ω.IsNondegenerate) :
    ω.Compatible J ↔ ∀ x, (h.symplecticFormAt x).Compatible (J.almostComplexStructureAt x) := by
  simp only [ContMDiffTwoForm.compatible_iff, TauCeti.SymplecticForm.compatible_iff, forall_and,
    h.invariant_iff, h.tames_iff]

/-- A compatible pair is a linear compatible pair on every fibre. -/
theorem Compatible.compatibleAt (h : ω.Compatible J) (x : M) :
    (h.isNondegenerate.symplecticFormAt x).Compatible (J.almostComplexStructureAt x) :=
  h.isNondegenerate.compatible_iff.1 h x

/-! ### Convexity -/

/-- The two-forms that tame a fixed complex structure form a convex set. -/
theorem convex_setOf_tames (J : ContMDiffComplexStructure I m F V) :
    Convex ℝ {ω : ContMDiffTwoForm I n F V | ω.Tames J} := by
  intro ω hω ω' hω' a b ha hb hab x v hv
  have h₁ := hω x v hv
  have h₂ := hω' x v hv
  simp only [bilinFormAt_add, bilinFormAt_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul]
  rcases ha.lt_or_eq with ha | rfl
  · positivity
  · rw [zero_add] at hab
    subst hab
    simpa using h₂

/-- The two-forms invariant under a fixed complex structure form a convex set. -/
theorem convex_setOf_invariant (J : ContMDiffComplexStructure I m F V) :
    Convex ℝ {ω : ContMDiffTwoForm I n F V | ω.Invariant J} := by
  intro ω hω ω' hω' a b _ _ _ x v w
  simp only [bilinFormAt_add, bilinFormAt_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hω x v w, hω' x v w]

/-- The two-forms compatible with a fixed complex structure form a convex set. -/
theorem convex_setOf_compatible (J : ContMDiffComplexStructure I m F V) :
    Convex ℝ {ω : ContMDiffTwoForm I n F V | ω.Compatible J} := by
  have h : {ω : ContMDiffTwoForm I n F V | ω.Compatible J} =
      {ω | ω.Invariant J} ∩ {ω | ω.Tames J} := by
    ext ω
    exact compatible_iff
  rw [h]
  exact (convex_setOf_invariant J).inter (convex_setOf_tames J)

end Predicates

/-! ### Transport along isomorphisms of bundles -/

section Pushforward

variable {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] {V₁ V₂ : M → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul ℝ (V₁ x)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul ℝ (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  (Φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
  (hΦ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
    (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (Φ p.proj p.snd)))
  (hΦ' : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) m
    (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (Φ p.proj p.snd)))
  {ω : ContMDiffTwoForm I n F₁ V₁} {J : ContMDiffComplexStructure I m F₁ V₁}

/-- The bilinear form of a transported form, evaluated on a pair and the transported structure,
is that of the original form on the pair moved back. -/
private theorem bilinFormAt_pushforward_apply (x : M) (u v : V₂ x) :
    (pushforward Φ hΦ ω).bilinFormAt x u v = ω.bilinFormAt x ((Φ x).symm u) ((Φ x).symm v) := by
  simp [bilinFormAt_pushforward]

/-- Transport along an isomorphism of bundles preserves tameness, when the form and the complex
structure move together. -/
theorem Tames.pushforward (h : ω.Tames J) :
    (ContMDiffTwoForm.pushforward Φ hΦ ω).Tames (J.pushforward Φ hΦ') := by
  intro x v hv
  rw [bilinFormAt_pushforward_apply, ContMDiffComplexStructure.pushforward_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  exact h x _ (by simpa using hv)

/-- Transport along an isomorphism of bundles preserves invariance, when the form and the complex
structure move together. -/
theorem Invariant.pushforward (h : ω.Invariant J) :
    (ContMDiffTwoForm.pushforward Φ hΦ ω).Invariant (J.pushforward Φ hΦ') := by
  intro x v w
  simp only [bilinFormAt_pushforward_apply, ContMDiffComplexStructure.pushforward_apply,
    ContinuousLinearEquiv.symm_apply_apply, h x]

/-- Transport along an isomorphism of bundles preserves compatibility, when the form and the
complex structure move together. -/
theorem Compatible.pushforward (h : ω.Compatible J) :
    (ContMDiffTwoForm.pushforward Φ hΦ ω).Compatible (J.pushforward Φ hΦ') :=
  ⟨h.invariant.pushforward Φ hΦ hΦ', h.tames.pushforward Φ hΦ hΦ'⟩

end Pushforward

/-! ### The tangent bundle -/

section Tangent

variable [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  {ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M))}
  {J : ContMDiffComplexStructure I ⊤ EB (TangentSpace I : M → Type _)}

/-- On the tangent bundle, tameness is Tau Ceti's tameness of the corresponding smooth two-form and
almost complex structure. -/
@[simp]
theorem tames_tangentEquiv_iff :
    (tangentEquiv ω).Tames (ContMDiffComplexStructure.tangentEquiv J).toSmooth ↔ ω.Tames J := by
  simp [TauCeti.SmoothTwoForm.tames_iff, tames_iff]

/-- On the tangent bundle, invariance is Tau Ceti's invariance of the corresponding smooth two-form
and almost complex structure. -/
@[simp]
theorem invariant_tangentEquiv_iff :
    (tangentEquiv ω).Invariant (ContMDiffComplexStructure.tangentEquiv J).toSmooth ↔
      ω.Invariant J := by
  simp [TauCeti.SmoothTwoForm.invariant_iff, invariant_iff]

/-- On the tangent bundle, compatibility is Tau Ceti's compatibility of the corresponding smooth
two-form and almost complex structure. -/
@[simp]
theorem compatible_tangentEquiv_iff :
    (tangentEquiv ω).Compatible (ContMDiffComplexStructure.tangentEquiv J).toSmooth ↔
      ω.Compatible J := by
  rw [compatible_iff, ← invariant_tangentEquiv_iff, ← tames_tangentEquiv_iff]
  exact ⟨fun h ↦ ⟨h.invariant, h.tames⟩, fun h ↦ ⟨h.1, h.2⟩⟩

end Tangent

end ContMDiffTwoForm

/-! ### The form of a metric and a complex structure -/

namespace ContMDiffComplexStructure

/-- The bilinear section `g ∘ J` of a metric and a complex structure, `(u, v) ↦ g(J u, v)`. -/
private def metricComp (g : ContMDiffRiemannianMetric I n F V)
    (J : ContMDiffComplexStructure I n F V) : TauCeti.Manifold.BilinearSection I F V ℝ n :=
  ⟨fun x ↦ (g.inner x).comp (J x), g.contMDiff.clm_bundle_comp J.toEndomorphism.contMDiff⟩

/-- The bilinear section `(g(J u, v) - g(J v, u)) / 2`, which by the symmetry of `g` is
`ω_{g,J}`. -/
private def compatibleBilin (g : ContMDiffRiemannianMetric I n F V)
    (J : ContMDiffComplexStructure I n F V) : TauCeti.Manifold.BilinearSection I F V ℝ n :=
  (2 : ℝ)⁻¹ • (metricComp g J - TauCeti.Manifold.transposeBilinearSection (metricComp g J))

private theorem compatibleBilin_apply (g : ContMDiffRiemannianMetric I n F V)
    (J : ContMDiffComplexStructure I n F V) (x : M) (u v : V x) :
    compatibleBilin g J x u v = (2 : ℝ)⁻¹ * (g.inner x (J x u) v - g.inner x u (J x v)) := by
  simp [compatibleBilin, metricComp, g.symm x u (J x v)]

variable [FiniteDimensional ℝ F]

/-- The alternating map of `ω_{g,J}` on the fibre over `x`. -/
private def compatibleFormAt (g : ContMDiffRiemannianMetric I n F V)
    (J : ContMDiffComplexStructure I n F V) (x : M) : V x [⋀^Fin 2]→L[ℝ] ℝ :=
  haveI := VectorBundle.finiteDimensional (R := ℝ) (F := F) (E := V) x
  haveI := FiberBundle.t2Space (E := V) F x
  AlternatingMap.toContinuousAlternatingMap
    (LinearMap.IsAlt.toAlternatingMap (ω := (compatibleBilin g J x).toBilinForm) fun v ↦ by
      simp [compatibleBilin_apply, g.symm x v (J x v)])

private theorem compatibleFormAt_apply (g : ContMDiffRiemannianMetric I n F V)
    (J : ContMDiffComplexStructure I n F V) (x : M) (v : Fin 2 → V x) :
    compatibleFormAt g J x v = compatibleBilin g J x (v 0) (v 1) := by
  simp only [compatibleFormAt, AlternatingMap.coe_toContinuousAlternatingMap]
  exact LinearMap.IsAlt.toAlternatingMap_apply _ v

/-- The two-form `ω_{g,J}(u, v) = (g(J u, v) - g(u, J v)) / 2` of a bundle metric `g` and a
complex structure `J`. It is compatible with `J` (`compatible_compatibleForm`). For the Euclidean
inner product and the standard complex structure of `StdSpace ι` the formula gives `stdForm ι`. -/
def compatibleForm (g : ContMDiffRiemannianMetric I n F V)
    (J : ContMDiffComplexStructure I n F V) : ContMDiffTwoForm I n F V where
  toFun := compatibleFormAt g J
  contMDiff_toFun x :=
    TauCeti.contMDiffAt_continuousAlternatingMap_bundle_of_bilinear
      ((compatibleBilin g J).contMDiff x) fun _ v ↦ compatibleFormAt_apply g J _ v

/-- The value of `ω_{g,J}` on two vectors `v 0`, `v 1` is
`(g(J (v 0), v 1) - g(v 0, J (v 1))) / 2`. -/
@[simp]
theorem compatibleForm_apply (g : ContMDiffRiemannianMetric I n F V)
    (J : ContMDiffComplexStructure I n F V) (x : M) (v : Fin 2 → V x) :
    compatibleForm g J x v =
      (2 : ℝ)⁻¹ * (g.inner x (J x (v 0)) (v 1) - g.inner x (v 0) (J x (v 1))) :=
  (compatibleFormAt_apply g J x v).trans (compatibleBilin_apply g J x (v 0) (v 1))

/-- The form `ω_{g,J}` is compatible with `J`. -/
theorem compatible_compatibleForm (g : ContMDiffRiemannianMetric I n F V)
    (J : ContMDiffComplexStructure I n F V) : (compatibleForm g J).Compatible J where
  invariant x v w := by
    simp only [ContMDiffTwoForm.bilinFormAt_apply, compatibleForm_apply]
    simp [g.symm x (J x v) w, g.symm x v (J x w)]
    ring
  tames x v hv := by
    have h₁ := g.pos x v hv
    have h₂ := g.pos x (J x v) ((J.injective x).ne_iff' (map_zero _) |>.2 hv)
    simp only [ContMDiffTwoForm.bilinFormAt_apply, compatibleForm_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, apply_apply, map_neg]
    linarith

end ContMDiffComplexStructure

end SymplecticGeometry.Bundle

end
