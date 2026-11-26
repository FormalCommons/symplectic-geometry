/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ComplexStructure
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Riemannian.PolarEnd
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar
import SymplecticGeometry.LinearAlgebra.SesquilinearForm

/-!
# Tame and compatible pairs on a vector bundle

Let `ω` be a two-form and `J` a complex structure on a real vector bundle `V → M`, of possibly
different regularities. This file defines when `ω` tames `J` (`ω(v, J v) > 0` for every nonzero
`v`), when `ω` is `J`-invariant (`ω(J v, J w) = ω(v, w)`), and when the pair is compatible (both).
These follow Tau Ceti's `TauCeti.SmoothTwoForm.Tames`, `Invariant` and `Compatible` for the
tangent bundle, and for a nondegenerate form they are, on each fibre, Tau Ceti's linear
`TauCeti.SymplecticForm.Tames`, `Invariant` and `Compatible`.

## Main definitions

* `SymplecticGeometry.Bundle.ContMDiffTwoForm.Tames`, `Invariant` and `Compatible`.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.compatibleForm g J`: for a bundle metric
  `g` and a complex structure `J`, the two-form `ω_{g,J}(u, v) = (g(J u, v) - g(u, J v)) / 2`.
  With this sign, the formula for the Euclidean inner product and the standard complex structure
  `J₀` of `StdSpace ι` gives the standard form `stdForm ι`
  (`SymplecticGeometry.stdForm_apply_eq_inner_sub_inner`).
* `SymplecticGeometry.Bundle.ContMDiffTwoForm.Compatible.metric hc`: for a two-form `ω` compatible
  with a complex structure `J`, the bundle metric `g(u, v) = ω(u, J v)`; going the other way from
  `compatibleForm`.
* `SymplecticGeometry.Bundle.ContMDiffTwoForm.IsNondegenerate.polarComplexStructure g hω`: for a
  bundle metric `g` and a nondegenerate two-form `ω`, the complex structure `J_{g,ω}` whose value
  at each point is Tau Ceti's polar complex structure of `ω_x` for the inner product `g x`.

## Main results

* `Tames.isNondegenerate`, `Compatible.isNondegenerate`: a form taming some complex structure is
  nondegenerate.
* `IsNondegenerate.tames_iff`, `IsNondegenerate.invariant_iff`, `IsNondegenerate.compatible_iff`:
  for a nondegenerate form, the predicates are Tau Ceti's linear ones on every fibre.
* `Tames.pushforward`, `Invariant.pushforward`, `Compatible.pushforward`: transport along an
  isomorphism of bundles, moving the form and the complex structure together.
* `tames_tangentEquiv_iff`, `invariant_tangentEquiv_iff`, `compatible_tangentEquiv_iff`: on the
  tangent bundle, the predicates are Tau Ceti's; `compatible_tangentEquiv_symm_iff` reads
  compatibility the other way.
* `convex_setOfPred_tames`, `convex_setOfPred_invariant`, `convex_setOfPred_compatible`: the
  two-forms taming, invariant under, or compatible with a fixed complex structure form a convex set.
* `ContMDiffComplexStructure.compatible_compatibleForm`: `ω_{g,J}` is compatible with `J`.
* `ContMDiffComplexStructure.compatibleForm_apply_of_invariant`: for a metric `g` invariant under
  `J`, `ω_{g,J}(u, v) = g(J u, v)`.
* `ContMDiffComplexStructure.flat_compatibleForm`: the flat map of `ω_{g,J}` at `x` is
  `Bundle.ContMDiffRiemannianMetric.compatibleBilinAt g x (J x)`, and
  `ContMDiffComplexStructure.compatibleForm_eq_alternatingMapOfBilin`: the value of `ω_{g,J}` at
  `x` is the alternating map `Bundle.alternatingMapOfBilin` of that form.
* `ContMDiffTwoForm.Compatible.compatibleForm_metric`: for a compatible pair `(ω, J)`, the form
  `ω_{g,J}` of the metric `g = Compatible.metric` is `ω` again.
* `ContMDiffTwoForm.Compatible.metric_inner_apply_apply`: that metric is invariant under `J`.
* `ContMDiffComplexStructure.metric_compatible_compatibleForm`: conversely, for a metric `g`
  invariant under `J`, the metric of the pair `(ω_{g,J}, J)` is `g` again.
* `Bundle.mk_flatAt_mem_polarFormulaDomain`, `IsNondegenerate.mk_flat_mem_polarFormulaDomain`:
  the flat map of a nondegenerate alternating form lies in `Bundle.polarFormulaDomain`.
* `IsNondegenerate.polarFormulaAt_flat`: the polar formula of
  `Bundle.ContMDiffRiemannianMetric.polarFormulaAt` at the flat map of a nondegenerate form is
  Tau Ceti's linear polar complex structure.
* `IsNondegenerate.compatible_polarComplexStructure`, `apply_polarComplexStructure_apply` and
  `polarComplexStructure_eq_iff`: `J_{g,ω}` is the only complex structure compatible with `ω` and
  orthogonal for `g`.
* `IsNondegenerate.tames_lineMap_compatibleForm`: the segment from `ω` to `ω_{g,J_{g,ω}}` consists
  of forms taming `J_{g,ω}`.
* `ContMDiffComplexStructure.mk_mem_polarEndDomain`,
  `IsNondegenerate.polarEndAt_eq_polarComplexStructure`: the
  values of a complex structure lie in `Bundle.ContMDiffRiemannianMetric.polarEndDomain g`, and
  `Bundle.ContMDiffRiemannianMetric.polarEndAt g x B` is the value of `J_{g,ω}` at `x` when the
  flat map of `ω` at `x` is `compatibleBilinAt g x B`.
* `IsNondegenerate.polarComplexStructure_tangentEquiv`: on the tangent bundle, `J_{g,ω}` is Tau
  Ceti's `TauCeti.SmoothTwoForm.IsNondegenerate.polarComplexStructure`.
* `IsNondegenerate.exists_compatible`, `ContMDiffComplexStructure.exists_compatible`: over a
  Hausdorff σ-compact base, every nondegenerate two-form has a compatible complex structure, and
  every complex structure a compatible two-form.

## Implementation notes

The form `ω_{g,J}` is `ContMDiffTwoForm.ofBilinearSection` of the bilinear section
`x ↦ Bundle.ContMDiffRiemannianMetric.compatibleBilinAt g x (J x)`, which is `Cⁿ` by
`Bundle.ContMDiffRiemannianMetric.contMDiff_compatibleBilinAt`.
That constructor needs a model fibre of finite dimension, so `compatibleForm` assumes that `F` is
finite-dimensional.

The smoothness of `J_{g,ω}` is that of the polar formula on the bundle of bilinear forms
(`Bundle.ContMDiffRiemannianMetric.contMDiffOn_polarFormulaAt`), composed with the flat map of
`ω`; the fibres carry no norm, so its value at a point is stated through an equivalence of the
fibre with an inner product space that carries `g x` to the inner product. The existence of
compatible complex structures follows Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible` for the tangent bundle: take `J_{g,ω}`
for a bundle metric `g` given by `TauCeti.nonempty_contMDiffRiemannianMetric`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.5, §2.6
-/

public section

noncomputable section

open _root_.Bundle Set
open scoped Manifold RealInnerProductSpace

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

/-- Tameness is positivity of the bilinear form `ω_x(v, J v)` on every nonzero vector. -/
theorem tames_def : ω.Tames J ↔ ∀ (x : M) (v : V x), v ≠ 0 → 0 < ω.bilinFormAt x v (J x v) :=
  Iff.rfl

/-- Invariance is the identity `ω_x(J v, J w) = ω_x(v, w)` of bilinear forms on every fibre. -/
theorem invariant_def :
    ω.Invariant J ↔ ∀ (x : M) (v w : V x), ω.bilinFormAt x (J x v) (J x w) = ω.bilinFormAt x v w :=
  Iff.rfl

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

/-- Tameness does not depend on the regularity at which the complex structure is viewed. -/
@[simp]
theorem tames_ofLE_iff {l : ℕ∞} (h : l ≤ m) : ω.Tames (J.ofLE h) ↔ ω.Tames J := by
  simp only [tames_def, ContMDiffComplexStructure.ofLE_apply]

/-- `-ω` tames `-J` exactly when `ω` tames `J`. -/
@[simp]
theorem neg_tames_neg_iff : (-ω).Tames (-J) ↔ ω.Tames J := by
  simp only [tames_def, bilinFormAt_neg, ContMDiffComplexStructure.neg_apply,
    neg_apply, LinearMap.neg_apply, map_neg, neg_neg]

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
theorem convex_setOfPred_tames (J : ContMDiffComplexStructure I m F V) :
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
theorem convex_setOfPred_invariant (J : ContMDiffComplexStructure I m F V) :
    Convex ℝ {ω : ContMDiffTwoForm I n F V | ω.Invariant J} := by
  intro ω hω ω' hω' a b _ _ _ x v w
  simp only [bilinFormAt_add, bilinFormAt_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hω x v w, hω' x v w]

/-- The two-forms compatible with a fixed complex structure form a convex set. -/
theorem convex_setOfPred_compatible (J : ContMDiffComplexStructure I m F V) :
    Convex ℝ {ω : ContMDiffTwoForm I n F V | ω.Compatible J} := by
  have h : {ω : ContMDiffTwoForm I n F V | ω.Compatible J} =
      {ω | ω.Invariant J} ∩ {ω | ω.Tames J} := by
    ext ω
    exact compatible_iff
  rw [h]
  exact (convex_setOfPred_invariant J).inter (convex_setOfPred_tames J)

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

/-- A smooth two-form and a smooth almost complex structure in the sense of Tau Ceti are
compatible exactly when the corresponding two-form and complex structure on the tangent bundle
are. -/
@[simp]
theorem compatible_tangentEquiv_symm_iff {φ : TauCeti.SmoothTwoForm I M}
    {K : TauCeti.SmoothAlmostComplexStructure I M} :
    (tangentEquiv.symm φ).Compatible
        (ContMDiffComplexStructure.tangentEquiv.symm (K.toContMDiff ⊤)) ↔
      φ.Compatible K := by
  rw [← compatible_tangentEquiv_iff]
  simp

end Tangent

end ContMDiffTwoForm

/-! ### The form of a metric and a complex structure -/

namespace ContMDiffComplexStructure

/-- The bilinear section `x ↦ compatibleBilinAt g x (J x)` of a metric and a complex structure. -/
private def compatibleBilin (g : ContMDiffRiemannianMetric I n F V)
    (J : ContMDiffComplexStructure I n F V) : TauCeti.Manifold.BilinearSection I F V ℝ n :=
  ContMDiffSection.map g.compatibleBilinAt g.contMDiff_compatibleBilinAt J.toEndomorphism

variable [FiniteDimensional ℝ F]

/-- The two-form `ω_{g,J}(u, v) = (g(J u, v) - g(u, J v)) / 2` of a bundle metric `g` and a
complex structure `J`. It is compatible with `J` (`compatible_compatibleForm`). For the Euclidean
inner product and the standard complex structure of `StdSpace ι` the formula gives `stdForm ι`
(`SymplecticGeometry.stdForm_apply_eq_inner_sub_inner`). -/
def compatibleForm (g : ContMDiffRiemannianMetric I n F V)
    (J : ContMDiffComplexStructure I n F V) : ContMDiffTwoForm I n F V :=
  ContMDiffTwoForm.ofBilinearSection (compatibleBilin g J) fun x v ↦ by
    rw [compatibleBilin, ContMDiffSection.map_apply]
    exact g.isAlt_compatibleBilinAt x (J.toEndomorphism x) v

/-- The value of `ω_{g,J}` on two vectors `v 0`, `v 1` is
`(g(J (v 0), v 1) - g(v 0, J (v 1))) / 2`. -/
@[simp]
theorem compatibleForm_apply (g : ContMDiffRiemannianMetric I n F V)
    (J : ContMDiffComplexStructure I n F V) (x : M) (v : Fin 2 → V x) :
    compatibleForm g J x v =
      (2 : ℝ)⁻¹ * (g.inner x (J x (v 0)) (v 1) - g.inner x (v 0) (J x (v 1))) :=
  (ContMDiffTwoForm.ofBilinearSection_apply _ _ x v).trans <| by
    rw [compatibleBilin, ContMDiffSection.map_apply, g.compatibleBilinAt_apply]

/-- For a metric `g` invariant under `J`, `g(J u, J v) = g(u, v)`, the form `ω_{g,J}` is
`ω_{g,J}(u, v) = g(J u, v)`. -/
theorem compatibleForm_apply_of_invariant {g : ContMDiffRiemannianMetric I n F V}
    {J : ContMDiffComplexStructure I n F V}
    (hg : ∀ x (u v : V x), g.inner x (J x u) (J x v) = g.inner x u v) (x : M) (u v : V x) :
    compatibleForm g J x ![u, v] = g.inner x (J x u) v := by
  have h := hg x u (J x v)
  rw [apply_apply, map_neg] at h
  simp only [compatibleForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  linarith

/-- The form `ω_{g,J}` is compatible with `J`. -/
theorem compatible_compatibleForm (g : ContMDiffRiemannianMetric I n F V)
    (J : ContMDiffComplexStructure I n F V) : (compatibleForm g J).Compatible J where
  invariant x v w := by
    simp only [ContMDiffTwoForm.bilinFormAt_apply, compatibleForm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, apply_apply]
    rw [g.symm x (-v) (J x w), g.symm x v (J x w)]
    simp only [map_neg]
    ring
  tames x v hv := by
    have h₁ := g.pos x v hv
    have h₂ := g.pos x (J x v) ((J.injective x).ne_iff' (map_zero _) |>.2 hv)
    simp only [ContMDiffTwoForm.bilinFormAt_apply, compatibleForm_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, apply_apply, map_neg]
    linarith

/-- The value of `ω_{g,J}` at `x` is the alternating map of the form
`compatibleBilinAt g x (J x)`. -/
theorem compatibleForm_eq_alternatingMapOfBilin (g : ContMDiffRiemannianMetric I n F V)
    (J : ContMDiffComplexStructure I n F V) (x : M) :
    compatibleForm g J x = _root_.Bundle.alternatingMapOfBilin F (g.compatibleBilinAt x (J x))
      fun v ↦ by simpa using g.isAlt_compatibleBilinAt x (J x) v := by
  ext v
  simp

/-- The flat map of `ω_{g,J}` at `x` is the form `compatibleBilinAt g x (J x)`. -/
theorem flat_compatibleForm (g : ContMDiffRiemannianMetric I n F V)
    (J : ContMDiffComplexStructure I n F V) (x : M) :
    (compatibleForm g J).flat x = g.compatibleBilinAt x (J x) := by
  ext u v
  simp [ContMDiffTwoForm.flat_apply]

end ContMDiffComplexStructure

/-! ### The metric of a compatible pair -/

namespace ContMDiffTwoForm

variable {ω : ContMDiffTwoForm I n F V} {J : ContMDiffComplexStructure I n F V}

/-- The bilinear section `(u, v) ↦ -ω(J u, v)`, which for a compatible pair is `ω(u, J v)`. -/
private def compatibleMetricBilin (ω : ContMDiffTwoForm I n F V)
    (J : ContMDiffComplexStructure I n F V) : TauCeti.Manifold.BilinearSection I F V ℝ n :=
  -⟨fun x ↦ (ω.flat x).comp (J x), ω.contMDiff_flat.clm_bundle_comp J.toEndomorphism.contMDiff⟩

private theorem compatibleMetricBilin_apply (x : M) (u v : V x) :
    compatibleMetricBilin ω J x u v = -ω.bilinFormAt x (J x u) v := by
  simp [compatibleMetricBilin, flat_apply, bilinFormAt_apply]

/-- For a compatible pair, the bilinear section `-ω(J u, v)` is `ω(u, J v)`. -/
private theorem Compatible.compatibleMetricBilin_apply (hc : ω.Compatible J) (x : M)
    (u v : V x) : compatibleMetricBilin ω J x u v = ω.bilinFormAt x u (J x v) := by
  simpa [ContMDiffTwoForm.compatibleMetricBilin_apply] using
    neg_eq_iff_eq_neg.2 ((hc.compatibleAt x).invariant.apply_apply_eq_neg u v)

variable [FiniteDimensional ℝ F]

/-- The bundle metric `g(u, v) = ω(u, J v)` of a two-form `ω` compatible with a complex structure
`J`. It is the counterpart of `ContMDiffComplexStructure.compatibleForm`, which goes from a metric
to a form. -/
def Compatible.metric (hc : ω.Compatible J) : ContMDiffRiemannianMetric I n F V :=
  .ofPositiveDefiniteSection (compatibleMetricBilin ω J) <| by
    refine (TauCeti.Manifold.mem_positiveDefiniteBilinearSections _).2
      ⟨(TauCeti.Manifold.mem_symmetricBilinearSections _).2 fun x u v ↦ ?_,
      fun x v hv ↦ ?_⟩
    · rw [ContMDiffTwoForm.compatibleMetricBilin_apply x u v,
        hc.compatibleMetricBilin_apply x v u,
        (ω.isAlt_bilinFormAt x).neg_eq]
    · rw [hc.compatibleMetricBilin_apply]
      exact tames_def.1 hc.tames x v hv

/-- The metric of a compatible pair is `g(u, v) = ω(u, J v)`. -/
@[simp]
theorem Compatible.metric_inner (hc : ω.Compatible J) (x : M) (u v : V x) :
    hc.metric.inner x u v = ω.bilinFormAt x u (J x v) :=
  (ContMDiffRiemannianMetric.ofPositiveDefiniteSection_inner _ _ x u v).trans
    (hc.compatibleMetricBilin_apply x u v)

/-- The form `ω_{g,J}` of the metric `g` of a compatible pair `(ω, J)` is `ω` again. So
`Compatible.metric` is a right inverse of `ContMDiffComplexStructure.compatibleForm · J`. -/
@[simp]
theorem Compatible.compatibleForm_metric (hc : ω.Compatible J) :
    ContMDiffComplexStructure.compatibleForm hc.metric J = ω := by
  refine ext_bilinFormAt fun x ↦ LinearMap.ext₂ fun u v ↦ ?_
  have h := invariant_def.1 hc.invariant x u v
  simp only [bilinFormAt_apply, ContMDiffComplexStructure.compatibleForm_apply, metric_inner,
    Matrix.cons_val_zero, Matrix.cons_val_one, ContMDiffComplexStructure.apply_apply,
    map_neg] at h ⊢
  linarith

/-- The metric of a compatible pair `(ω, J)` is invariant under `J`:
`g(J u, J v) = g(u, v)`. -/
theorem Compatible.metric_inner_apply_apply (hc : ω.Compatible J) (x : M) (u v : V x) :
    hc.metric.inner x (J x u) (J x v) = hc.metric.inner x u v := by
  rw [metric_inner, metric_inner]
  exact invariant_def.1 hc.invariant x u (J x v)

/-- On each fibre, the metric of a compatible pair is the metric `ω_x(·, J_x ·)` of the linear
compatible pair. -/
theorem Compatible.symplecticFormAt_apply_apply_eq_metric_inner (hc : ω.Compatible J) (x : M)
    (u v : V x) :
    hc.isNondegenerate.symplecticFormAt x u (J.almostComplexStructureAt x v) =
      hc.metric.inner x u v := by
  rw [hc.metric_inner, ContMDiffComplexStructure.almostComplexStructureAt_apply,
    IsNondegenerate.symplecticFormAt_apply, bilinFormAt_apply]

end ContMDiffTwoForm

namespace ContMDiffComplexStructure

variable [FiniteDimensional ℝ F] {g : ContMDiffRiemannianMetric I n F V}
  {J : ContMDiffComplexStructure I n F V}

/-- For a metric `g` invariant under `J`, the metric of the compatible pair `(ω_{g,J}, J)` is `g`
again. So `ContMDiffTwoForm.Compatible.metric` is a left inverse of `compatibleForm · J` on the
metrics invariant under `J`. -/
theorem metric_compatible_compatibleForm
    (hg : ∀ x (u v : V x), g.inner x (J x u) (J x v) = g.inner x u v) :
    (compatible_compatibleForm g J).metric = g := by
  refine ContMDiffRiemannianMetric.ext fun x u v ↦ ?_
  rw [ContMDiffTwoForm.Compatible.metric_inner, ContMDiffTwoForm.bilinFormAt_apply,
    compatibleForm_apply_of_invariant hg]
  exact hg x u v

end ContMDiffComplexStructure

/-! ### The complex structure `J_{g,ω}` -/

namespace ContMDiffTwoForm

variable {ω : ContMDiffTwoForm I n F V}

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- The flat map of an alternating map `α` of two vectors of `V x` whose bilinear form is
nondegenerate lies in the domain of the polar formula: since `α` is alternating, the skew part of
its flat map is twice its bilinear form. -/
theorem _root_.Bundle.mk_flatAt_mem_polarFormulaDomain {x : M}
    {α : V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x}
    (hα : (MultilinearMap.toBilinMap α.toMultilinearMap :
      LinearMap.BilinForm ℝ (V x)).Nondegenerate) :
    (⟨x, _root_.Bundle.flatAt F α⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
      fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) ∈ _root_.Bundle.polarFormulaDomain F V := by
  set B : LinearMap.BilinForm ℝ (V x) := MultilinearMap.toBilinMap α.toMultilinearMap
  have hB : (_root_.Bundle.flatAt F α).toBilinForm = B := by
    ext v w
    simp [B]
  have h : B - B.flip = (2 : ℝ) • B := by
    ext v w
    simpa [B, two_smul, two_nsmul] using
      congr($((AlternatingMap.isAlt_toBilinMap α.toAlternatingMap).sub_flip_eq_two_smul) v w)
  rw [_root_.Bundle.mem_polarFormulaDomain_iff, hB, h]
  exact (TauCeti.BilinForm.nondegenerate_smul_iff (IsRegular.of_ne_zero two_ne_zero)).2 hα

/-- The flat map of a nondegenerate two-form lies in the domain of the polar formula. -/
theorem IsNondegenerate.mk_flat_mem_polarFormulaDomain (hω : ω.IsNondegenerate) (x : M) :
    (⟨x, ω.flat x⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ) fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) ∈
      _root_.Bundle.polarFormulaDomain F V := by
  rw [flat_def]
  exact _root_.Bundle.mk_flatAt_mem_polarFormulaDomain
    ((bilinFormAt_def ω x) ▸ hω.nondegenerate_bilinFormAt x)

variable [FiniteDimensional ℝ F]

/-- On a fibre, the polar formula of a bundle metric `g` at the flat map of a nondegenerate
two-form `ω` is Tau Ceti's polar complex structure of `ω_x` for the inner product `g x`: read
through any continuous linear equivalence `e` of `V x` with an inner product space that carries
`g x` to the inner product, it is `TauCeti.SymplecticForm.polarComplexStructure` of the form
carried along `e`. -/
theorem IsNondegenerate.polarFormulaAt_flat (hω : ω.IsNondegenerate)
    (g : ContMDiffRiemannianMetric I n F V) {x : M} {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (e : V x ≃L[ℝ] W)
    (he : ∀ u v, ⟪e u, e v⟫ = g.inner x u v) :
    g.polarFormulaAt x (ω.flat x) = e.symm.conjContinuousAlgEquiv (LinearMap.toContinuousLinearMap
      ((hω.symplecticFormAt x).transport e.toLinearEquiv).polarComplexStructure.toLinearMap) := by
  have hg : e.bilinearCongr (g.inner x) = innerSL ℝ := by
    ext u v
    rw [innerSL_apply_apply]
    simp [← he]
  have hs : e.bilinearCongr (ω.flat x) =
      ((hω.symplecticFormAt x).transport e.toLinearEquiv).toBilinForm.toContinuousBilinearMap := by
    ext u v
    simp
  have hJ := SymplecticGeometry.metricPolarFormula_eq ⟨innerSL ℝ, innerSL_mem_innerProducts⟩
    ((hω.symplecticFormAt x).transport e.toLinearEquiv)
  rw [metricPolarComplexStructure_innerSL] at hJ
  rw [g.polarFormulaAt_eq_conj
    (_root_.Bundle.mem_polarFormulaDomain_iff.1 (hω.mk_flat_mem_polarFormulaDomain x)) e, hg, hs]
  exact congrArg e.symm.conjContinuousAlgEquiv hJ

/-- The complex structure `J_{g,ω}` of a bundle metric `g` and a nondegenerate two-form `ω`: at each
point `x`, Tau Ceti's polar complex structure of `ω_x` for the inner product `g x`
(`polarComplexStructure_apply`). It is compatible with `ω` (`compatible_polarComplexStructure`)
and orthogonal for `g` (`apply_polarComplexStructure_apply`), and these two properties
characterize it (`polarComplexStructure_eq_iff`). -/
def IsNondegenerate.polarComplexStructure (g : ContMDiffRiemannianMetric I n F V)
    (hω : ω.IsNondegenerate) : ContMDiffComplexStructure I n F V where
  toEndomorphism := ⟨fun x ↦ g.polarFormulaAt x (ω.flat x),
    g.contMDiffOn_polarFormulaAt.comp_contMDiff ω.contMDiff_flat
      hω.mk_flat_mem_polarFormulaDomain⟩
  square_neg x := by
    obtain ⟨e, he⟩ := g.exists_continuousLinearEquiv_inner_eq x
    ext v
    simp [hω.polarFormulaAt_flat g e he]

variable {g : ContMDiffRiemannianMetric I n F V} (hω : ω.IsNondegenerate)

/-- At each point, `J_{g,ω}` is the polar formula of `g` at the flat map of `ω`. -/
theorem IsNondegenerate.polarComplexStructure_eq_polarFormulaAt (x : M) :
    hω.polarComplexStructure g x = g.polarFormulaAt x (ω.flat x) :=
  (rfl)

/-- The value of `J_{g,ω}` at `x`, read through a continuous linear equivalence `e` of `V x` with an
inner product space that carries `g x` to the inner product, is Tau Ceti's polar complex structure
of the form carried along `e`. -/
theorem IsNondegenerate.polarComplexStructure_apply {x : M} {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (e : V x ≃L[ℝ] W)
    (he : ∀ u v, ⟪e u, e v⟫ = g.inner x u v) (v : V x) :
    hω.polarComplexStructure g x v =
      e.symm (((hω.symplecticFormAt x).transport e.toLinearEquiv).polarComplexStructure (e v)) := by
  rw [polarComplexStructure_eq_polarFormulaAt, hω.polarFormulaAt_flat g e he]
  simp

/-- As an almost complex structure on the fibre, `J_{g,ω}` at `x` is Tau Ceti's polar complex
structure of `ω_x` carried along an equivalence `e` that carries `g x` to an inner product, then
carried back. -/
theorem IsNondegenerate.almostComplexStructureAt_polarComplexStructure {x : M} {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (e : V x ≃L[ℝ] W)
    (he : ∀ u v, ⟪e u, e v⟫ = g.inner x u v) :
    (hω.polarComplexStructure g).almostComplexStructureAt x =
      ((hω.symplecticFormAt x).transport e.toLinearEquiv).polarComplexStructure.transport
        e.toLinearEquiv.symm := by
  ext v
  rw [ContMDiffComplexStructure.almostComplexStructureAt_apply, hω.polarComplexStructure_apply e he,
    TauCeti.AlmostComplexStructure.transport_apply]
  simp

/-- `J_{g,ω}` is orthogonal for `g`. -/
@[simp]
theorem IsNondegenerate.apply_polarComplexStructure_apply (x : M) (u v : V x) :
    g.inner x (hω.polarComplexStructure g x u) (hω.polarComplexStructure g x v) =
      g.inner x u v := by
  obtain ⟨e, he⟩ := g.exists_continuousLinearEquiv_inner_eq x
  rw [← he, ← he, hω.polarComplexStructure_apply e he, hω.polarComplexStructure_apply e he]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  exact TauCeti.SymplecticForm.inner_polarComplexStructure_apply_apply _ _ _

variable (g) in
/-- `J_{g,ω}` is compatible with `ω`. -/
theorem IsNondegenerate.compatible_polarComplexStructure :
    ω.Compatible (hω.polarComplexStructure g) :=
  hω.compatible_iff.2 fun x ↦ by
    obtain ⟨e, he⟩ := g.exists_continuousLinearEquiv_inner_eq x
    rw [hω.almostComplexStructureAt_polarComplexStructure e he]
    have h := ((hω.symplecticFormAt x).transport
      e.toLinearEquiv).compatible_polarComplexStructure.transport e.toLinearEquiv.symm
    rwa [TauCeti.SymplecticForm.transport_symm_transport] at h

/-- `J_{g,ω}` is the only complex structure that is orthogonal for `g` and compatible with `ω`. -/
theorem IsNondegenerate.polarComplexStructure_eq_iff {J : ContMDiffComplexStructure I n F V} :
    hω.polarComplexStructure g = J ↔
      (∀ x u v, g.inner x (J x u) (J x v) = g.inner x u v) ∧ ω.Compatible J := by
  refine ⟨?_, fun ⟨hJ, hc⟩ ↦ ContMDiffComplexStructure.ext fun x v ↦ ?_⟩
  · rintro rfl
    exact ⟨hω.apply_polarComplexStructure_apply, hω.compatible_polarComplexStructure g⟩
  obtain ⟨e, he⟩ := g.exists_continuousLinearEquiv_inner_eq x
  have hK : ((hω.symplecticFormAt x).transport e.toLinearEquiv).polarComplexStructure =
      (J.almostComplexStructureAt x).transport e.toLinearEquiv := by
    refine TauCeti.SymplecticForm.polarComplexStructure_eq_iff.2 ⟨fun u w ↦ ?_, ?_⟩
    · simp [he, hJ, ← he (e.symm u)]
    · exact (TauCeti.SymplecticForm.compatible_transport_iff _ _ _).2
        ((hω.compatible_iff.1 hc) x)
  rw [hω.polarComplexStructure_apply e he, hK]
  simp

variable (g) in
/-- For `t ∈ [0, 1]`, the form `(1 - t) • ω + t • ω_{g,J_{g,ω}}` on the segment from `ω` to the
form of `g` and `J_{g,ω}` tames `J_{g,ω}`, as both ends do; in particular it is nondegenerate
(`Tames.isNondegenerate`). -/
theorem IsNondegenerate.tames_lineMap_compatibleForm {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (AffineMap.lineMap ω
      (ContMDiffComplexStructure.compatibleForm g (hω.polarComplexStructure g)) t).Tames
      (hω.polarComplexStructure g) :=
  (convex_setOfPred_tames (hω.polarComplexStructure g)).lineMap_mem
    (hω.compatible_polarComplexStructure g).tames
    (ContMDiffComplexStructure.compatible_compatibleForm g _).tames ht


/-! ### The polar formula on the endomorphism bundle -/

/-- For every complex structure `J`, the point `(x, J x)` of the endomorphism bundle lies in
`polarEndDomain g`: there `compatibleBilinAt g x (J x)` is the flat map of the nondegenerate
form `ω_{g,J}`. -/
theorem _root_.SymplecticGeometry.Bundle.ContMDiffComplexStructure.mk_mem_polarEndDomain
    (J : ContMDiffComplexStructure I n F V) (g : ContMDiffRiemannianMetric I n F V) (x : M) :
    (⟨x, J x⟩ : TotalSpace (F →L[ℝ] F) fun x ↦ V x →L[ℝ] V x) ∈ g.polarEndDomain := by
  rw [ContMDiffRiemannianMetric.mem_polarEndDomain_iff,
    ← ContMDiffComplexStructure.flat_compatibleForm]
  exact mem_polarFormulaDomain_iff.1 <|
    (ContMDiffComplexStructure.compatible_compatibleForm g J).isNondegenerate
    |>.mk_flat_mem_polarFormulaDomain x

/-- If the flat map of a nondegenerate two-form `ω` at `x` is `compatibleBilinAt g x B`, then
`polarEndAt g x B` is the value of `J_{g,ω}` at `x`. -/
theorem IsNondegenerate.polarEndAt_eq_polarComplexStructure {x : M} {B : V x →L[ℝ] V x}
    (h : ω.flat x = g.compatibleBilinAt x B) :
    g.polarEndAt x B = hω.polarComplexStructure g x := by
  rw [ContMDiffRiemannianMetric.polarEndAt_def, ← h,
    hω.polarComplexStructure_eq_polarFormulaAt]

/-- For bundle metrics `g₀` and `g₁` and a complex structure `J`, the polar formula of `g₁` at
`compatibleBilinAt g₀ x (J x)` is the value at `x` of `J_{g₁,ω_{g₀,J}}`. -/
theorem _root_.SymplecticGeometry.Bundle.ContMDiffComplexStructure.polarFormulaAt_compatibleBilinAt
    (g₀ g₁ : ContMDiffRiemannianMetric I n F V) (J : ContMDiffComplexStructure I n F V) (x : M) :
    g₁.polarFormulaAt x (g₀.compatibleBilinAt x (J x)) =
      IsNondegenerate.polarComplexStructure g₁
        (ContMDiffComplexStructure.compatible_compatibleForm g₀ J).isNondegenerate x := by
  rw [IsNondegenerate.polarComplexStructure_eq_polarFormulaAt,
    ContMDiffComplexStructure.flat_compatibleForm]

/-! ### The tangent bundle and existence -/

section Tangent

variable [FiniteDimensional ℝ EB] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- On the tangent bundle, `J_{g,ω}` is Tau Ceti's polar complex structure
`TauCeti.SmoothTwoForm.IsNondegenerate.polarComplexStructure` of the corresponding smooth two-form,
for the metric `g` installed as the Riemannian metric of `M`. -/
theorem IsNondegenerate.polarComplexStructure_tangentEquiv
    (g : ContMDiffRiemannianMetric I ((⊤ : ℕ∞) : WithTop ℕ∞) EB (TangentSpace I : M → Type _))
    {ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M))} (hω : ω.IsNondegenerate) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) EB
      (fun x : M ↦ TangentSpace I x) :=
        _root_.Bundle.instIsContMDiffRiemannianBundle g
    (ContMDiffComplexStructure.tangentEquiv (hω.polarComplexStructure g)).toSmooth =
      (isNondegenerate_tangentEquiv_iff.2 hω).polarComplexStructure := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) EB (fun x : M ↦ TangentSpace I x) :=
    _root_.Bundle.instIsContMDiffRiemannianBundle g
  set K := (ContMDiffComplexStructure.tangentEquiv (hω.polarComplexStructure g)).toSmooth
  -- Both are orthogonal for `g` and compatible with `ω` on each fibre, which characterizes Tau
  -- Ceti's linear polar complex structure.
  have hc := compatible_tangentEquiv_iff.2 (hω.compatible_polarComplexStructure g)
  refine TauCeti.SmoothAlmostComplexStructure.ext fun x v ↦ ?_
  have hK : ((isNondegenerate_tangentEquiv_iff.2 hω).symplecticFormAt x).polarComplexStructure =
      K.almostComplexStructureAt x :=
    TauCeti.SymplecticForm.polarComplexStructure_eq_iff.2
      ⟨fun u w ↦ by
        simp only [K, TauCeti.SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
          TauCeti.ContMDiffAlmostComplexStructure.toSmooth_toEndomorphism,
          ContMDiffComplexStructure.tangentEquiv_toEndomorphism]
        -- The inner product of the installed Riemannian bundle is `g` by definition.
        exact hω.apply_polarComplexStructure_apply (g := g) x u w, hc.compatibleAt x⟩
  rw [TauCeti.SmoothTwoForm.IsNondegenerate.polarComplexStructure_apply, hK,
    TauCeti.SmoothAlmostComplexStructure.almostComplexStructureAt_apply]

end Tangent

section Existence

variable [FiniteDimensional ℝ EB] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [ContMDiffVectorBundle n F V I]

/-- **Existence of compatible complex structures.** Over a Hausdorff σ-compact base, every
nondegenerate two-form on a vector bundle of finite rank is compatible with some complex structure
of the same regularity: `J_{g,ω}` for any bundle metric `g`. -/
theorem IsNondegenerate.exists_compatible {ω : ContMDiffTwoForm I n F V}
    (hω : ω.IsNondegenerate) : ∃ J : ContMDiffComplexStructure I n F V, ω.Compatible J := by
  obtain ⟨g⟩ := TauCeti.nonempty_contMDiffRiemannianMetric (IB := I) (n := n) (F := F) (E := V)
  exact ⟨hω.polarComplexStructure g, hω.compatible_polarComplexStructure g⟩

/-- **Existence of compatible forms.** Over a Hausdorff σ-compact base, every complex structure on
a vector bundle of finite rank is compatible with some two-form of the same regularity:
`ω_{g,J}` for any bundle metric `g`. -/
theorem _root_.SymplecticGeometry.Bundle.ContMDiffComplexStructure.exists_compatible
    (J : ContMDiffComplexStructure I n F V) :
    ∃ ω : ContMDiffTwoForm I n F V, ω.Compatible J := by
  obtain ⟨g⟩ := TauCeti.nonempty_contMDiffRiemannianMetric (IB := I) (n := n) (F := F) (E := V)
  exact ⟨J.compatibleForm g, J.compatible_compatibleForm g⟩

end Existence

end ContMDiffTwoForm

end SymplecticGeometry.Bundle

end
