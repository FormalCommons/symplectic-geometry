/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import SymplecticGeometry.Analysis.InnerProductSpace.Symplectic.PolarComplexStructure.Smooth
public import SymplecticGeometry.Topology.Algebra.Module.BilinearForm
public import SymplecticGeometry.Topology.FiberBundle.Basic
public import SymplecticGeometry.Topology.VectorBundle.Coordinates
public import TauCeti.Topology.VectorBundle.Coordinates

/-!
# The polar formula on the bundles of bilinear forms and of endomorphisms

Let `g` be a bundle metric on a real vector bundle `V → M` of finite rank. For a continuous
bilinear form `σ` on a fibre `V x` whose skew part is nondegenerate, this file defines the
endomorphism `J_{g,σ}` of `V x` (`Bundle.ContMDiffRiemannianMetric.polarFormulaAt g x σ`): the
formula `TauCeti.metricPolarFormula` applied to the pair `(g x, σ)`, read on a Euclidean space
through a linear equivalence of `V x` with it. It shows that this does not depend on the
equivalence, and that it is a `Cⁿ` map from the bundle of bilinear forms to the endomorphism bundle
on the open set where it is defined. At the flat map of a nondegenerate two-form it is the
complex structure `J_{g,ω}` of the bundle, which is built from it in
`SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic`.

For an endomorphism `B` of `V x`, it then defines the alternating form
`(u, v) ↦ (g(B u, v) - g(u, B v)) / 2` and the endomorphism `J_{g,ω_{g,B}}` of `V x` obtained by
applying the polar formula to it, and shows that the latter is a `Cⁿ` map from the endomorphism
bundle to itself on the open set where it is defined. At the value `B = J x` of a complex
structure, the form is the flat map of `ω_{g,J}`.

## Main definitions

* `Bundle.polarFormulaDomain F V`: the points `(x, σ)` of the bundle of bilinear forms where the
  skew part of `σ` is nondegenerate.
* `Bundle.euclideanEquivAt F V x`: the equivalence of `V x` with a Euclidean space given by the
  trivialization at `x`.
* `Bundle.ContMDiffRiemannianMetric.polarFormulaAt g x σ`: the endomorphism `J_{g,σ}` of `V x`.
* `Bundle.ContMDiffRiemannianMetric.compatibleBilinAt g x B`: the form
  `(u, v) ↦ (g(B u, v) - g(u, B v)) / 2` on `V x`, for an endomorphism `B` of `V x`.
* `Bundle.ContMDiffRiemannianMetric.polarEndDomain g`: the points `(x, B)` of the endomorphism
  bundle where `compatibleBilinAt g x B` is nondegenerate.
* `Bundle.ContMDiffRiemannianMetric.polarEndAt g x B`: the endomorphism `J_{g,ω_{g,B}}` of `V x`.

## Main results

* `Bundle.isOpen_polarFormulaDomain`: in finite rank, the domain is open.
* `Bundle.ContMDiffRiemannianMetric.polarFormulaAt_eq_conj`: on the domain, `J_{g,σ}` is the
  formula read through any linear equivalence of `V x` with a finite-dimensional inner product
  space.
* `Bundle.ContMDiffRiemannianMetric.contMDiffAt_inCoordinates_inner`: along a `Cⁿ` map into the
  base, the reading of a metric of class `Cⁿ` in a trivialization is `Cⁿ`.
* `Bundle.ContMDiffRiemannianMetric.contMDiffOn_polarFormulaAt`: for a metric of class `Cⁿ`, the
  map `(x, σ) ↦ (x, J_{g,σ})` is `Cⁿ` on the domain.
* `Bundle.ContMDiffRiemannianMetric.exists_continuousLinearEquiv_inner_eq`: each fibre of a
  bundle metric of finite rank is isometric to a Euclidean space.
* `Bundle.ContMDiffRiemannianMetric.contMDiff_compatibleBilinAt`: for a metric of class `Cⁿ`, the
  map `(x, B) ↦ (x, compatibleBilinAt g x B)` is `Cⁿ`.
* `Bundle.ContMDiffRiemannianMetric.isOpen_polarEndDomain` and
  `Bundle.ContMDiffRiemannianMetric.contMDiffOn_polarEndAt`: in finite rank, `polarEndDomain g` is
  open, and for a metric of class `Cⁿ` the map `(x, B) ↦ (x, J_{g,ω_{g,B}})` is `Cⁿ` on it.

## Implementation notes

The fibres of `V` carry no norm, so the formula, which needs an inner product space, is applied on
the Euclidean space `EuclideanSpace ℝ (Fin (finrank ℝ F))`, reached from `V x` through the
trivialization at `x`. The proof of `contMDiffOn_polarFormulaAt` adapts that of Tau Ceti's private
`TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_polarEnd`
(`TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/Polar.lean`): it reads the map in the
trivialization at a base point, where it becomes the formula at the coordinate readings of the
metric and of the form, conjugated by a constant equivalence. Here the form is a coordinate of the
total space instead of a fixed section, and the formula is smooth by
`TauCeti.contDiffOn_metricPolarFormula`. The domain is open by
`FiberBundle.isOpen_of_forall_mem_iff_snd_mem`, since each trivialization reads it as the open
set `ContinuousLinearMap.isOpen_setOf_nondegenerate_toBilinForm_sub_flip` of the model fibre.

The form `compatibleBilinAt g x B` is built from `(g x).comp B` and Mathlib's
`ContinuousLinearMap.precomp`, so that the fibres need no norm. In a trivialization it reads as
a fixed expression in the readings of `g` and of `B`, which gives `contMDiff_compatibleBilinAt`;
`polarEndDomain g` and `polarEndAt g` are then `polarFormulaDomain F V` and `polarFormulaAt g`
pulled back along it.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.5.6
-/

public section

noncomputable section

open Module Set Filter
open scoped Manifold Topology RealInnerProductSpace

namespace Bundle

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)]

/-! ### The domain -/

variable (F V) in
/-- The points `(x, σ)` of the bundle of continuous bilinear forms on `V` at which the skew part
`σ - σᵀ` of `σ` is nondegenerate. -/
def polarFormulaDomain :
    Set (TotalSpace (F →L[ℝ] F →L[ℝ] ℝ) fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) :=
  {q | (q.snd.toBilinForm - q.snd.toBilinForm.flip).Nondegenerate}

@[simp]
theorem mem_polarFormulaDomain_iff
    {q : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ) fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ} :
    q ∈ polarFormulaDomain F V ↔ (q.snd.toBilinForm - q.snd.toBilinForm.flip).Nondegenerate :=
  Iff.rfl

variable [TopologicalSpace M] [ChartedSpace HB M]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

/-- In finite rank, the domain of the polar formula is open in the bundle of bilinear forms. -/
theorem isOpen_polarFormulaDomain [FiniteDimensional ℝ F] :
    IsOpen (polarFormulaDomain F V) := by
  refine FiberBundle.isOpen_of_forall_mem_iff_snd_mem
    ContinuousLinearMap.isOpen_setOf_nondegenerate_toBilinForm_sub_flip fun b q hq ↦ ?_
  -- In the fibre coordinates of the trivialization, a form becomes its carrying along a linear
  -- equivalence.
  have hy : q.proj ∈ (trivializationAt F V b).baseSet := by
    simpa using hq
  rw [mem_polarFormulaDomain_iff, Set.mem_ofPred_eq, hom_trivializationAt_apply,
    ContinuousLinearMap.inCoordinates_eq_arrowCongr_arrowCongr hy,
    ContinuousLinearEquiv.nondegenerate_arrowCongr_sub_flip_iff]

/-! ### The polar formula on a fibre -/

variable (F V) in
/-- The continuous linear equivalence of the fibre `V x` with the Euclidean space
`EuclideanSpace ℝ (Fin (finrank ℝ F))`: the fibre equivalence of the trivialization at `x`,
followed by Mathlib's `ContinuousLinearEquiv.ofFinrankEq`. -/
def euclideanEquivAt [FiniteDimensional ℝ F] (x : M) :
    V x ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ F)) :=
  ((trivializationAt F V x).continuousLinearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt' x)).trans
    (.ofFinrankEq finrank_euclideanSpace_fin.symm)

variable (F V) in
theorem euclideanEquivAt_def [FiniteDimensional ℝ F] (x : M) :
    euclideanEquivAt F V x =
      ((trivializationAt F V x).continuousLinearEquivAt ℝ x
        (FiberBundle.mem_baseSet_trivializationAt' x)).trans
        (.ofFinrankEq finrank_euclideanSpace_fin.symm) :=
  (rfl)

/-- Carrying a metric and a form along a linear equivalence with an inner product space gives a
point of the domain of `TauCeti.metricPolarFormula` exactly when the skew part of the form is
nondegenerate. -/
theorem ContMDiffRiemannianMetric.mem_polarDomain_arrowCongr {n : WithTop ℕ∞}
    (g : ContMDiffRiemannianMetric I n F V) {x : M} {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] (e : V x ≃L[ℝ] W) {σ : V x →L[ℝ] V x →L[ℝ] ℝ}
    (hσ : (σ.toBilinForm - σ.toBilinForm.flip).Nondegenerate) :
    (e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (g.inner x),
      e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) σ) ∈ TauCeti.polarDomain W :=
  TauCeti.mem_polarDomain_iff.2 ⟨fun v hv ↦ by simpa using g.pos x (e.symm v) (by simpa using hv),
    e.nondegenerate_arrowCongr_sub_flip_iff.2 hσ⟩

/-- Along a map `f` of class `Cⁿ` into the base, the reading of a bundle metric of class `Cⁿ` in
the trivialization at `f y`, `y' ↦ inCoordinates … (f y) (f y') (f y) (f y') (g (f y'))`, is of
class `Cⁿ` at `y`. -/
theorem ContMDiffRiemannianMetric.contMDiffAt_inCoordinates_inner {n : WithTop ℕ∞}
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    (g : ContMDiffRiemannianMetric I n F V) {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {f : N → M} {y : N} (hf : ContMDiffAt IN I n f y) :
    ContMDiffAt IN 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) n
      (fun y' ↦ ContinuousLinearMap.inCoordinates F V (F →L[ℝ] ℝ)
        (fun x ↦ V x →L[ℝ] Trivial M ℝ x) (f y) (f y') (f y) (f y') (g.inner (f y'))) y :=
  ((contMDiffAt_hom_bundle fun y' ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
    (E := fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) (f y') (g.inner (f y'))).1
    ((g.contMDiff (f y)).comp y hf)).2

namespace ContMDiffRiemannianMetric

variable [FiniteDimensional ℝ F] {n : WithTop ℕ∞} (g : ContMDiffRiemannianMetric I n F V)

/-- Each fibre of a bundle metric of finite rank is isometric to a Euclidean space: some continuous
linear equivalence `e` of `V x` with `EuclideanSpace ℝ (Fin (finrank ℝ F))` carries `g x` to the
standard inner product. -/
theorem exists_continuousLinearEquiv_inner_eq (x : M) :
    ∃ e : V x ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ F)),
      ∀ u v, ⟪e u, e v⟫ = g.inner x u v := by
  let e₁ := (trivializationAt F V x).continuousLinearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt' x)
  let g₁ : SymplecticGeometry.innerProducts F :=
    ⟨e₁.arrowCongr (e₁.arrowCongr (.refl ℝ ℝ)) (g.inner x),
      SymplecticGeometry.mem_innerProducts.2 ⟨fun u v ↦ by simpa using g.symm x _ _,
        fun v hv ↦ by simpa using g.pos x (e₁.symm v) (by simpa using hv)⟩⟩
  obtain ⟨e₂, he₂⟩ := SymplecticGeometry.innerProducts.exists_transport_eq_innerSL g₁
  refine ⟨e₁.trans e₂, fun u v ↦ ?_⟩
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
    (SymplecticGeometry.innerProducts.transport_eq_innerSL_iff e₂ g₁).1 he₂]
  simp [g₁]

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

/-- The polar formula `J_{g,σ}` of a bundle metric `g` and a continuous bilinear form `σ` on the
fibre `V x`: the formula `TauCeti.metricPolarFormula` of the pair `(g x, σ)`, carried to the
Euclidean space `EuclideanSpace ℝ (Fin (finrank ℝ F))` along `Bundle.euclideanEquivAt F V x` and
conjugated back.
Where the skew part of `σ` is nondegenerate, the choice of the equivalence does not matter
(`polarFormulaAt_eq_conj`). -/
def polarFormulaAt (x : M) (σ : V x →L[ℝ] V x →L[ℝ] ℝ) : V x →L[ℝ] V x :=
  (euclideanEquivAt F V x).symm.conjContinuousAlgEquiv (TauCeti.metricPolarFormula
    ((euclideanEquivAt F V x).arrowCongr
      ((euclideanEquivAt F V x).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (g.inner x))
    ((euclideanEquivAt F V x).arrowCongr
      ((euclideanEquivAt F V x).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) σ))

theorem polarFormulaAt_def (x : M) (σ : V x →L[ℝ] V x →L[ℝ] ℝ) :
    g.polarFormulaAt x σ =
      (euclideanEquivAt F V x).symm.conjContinuousAlgEquiv (TauCeti.metricPolarFormula
        ((euclideanEquivAt F V x).arrowCongr
          ((euclideanEquivAt F V x).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (g.inner x))
        ((euclideanEquivAt F V x).arrowCongr
          ((euclideanEquivAt F V x).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) σ)) :=
  (rfl)

/-- **Independence of the equivalence.** Where the skew part of `σ` is nondegenerate, `J_{g,σ}` is
the polar formula of the pair `(g x, σ)` carried along any linear equivalence `e` of `V x` with a
finite-dimensional inner product space, conjugated back by `e`. -/
theorem polarFormulaAt_eq_conj {x : M} {σ : V x →L[ℝ] V x →L[ℝ] ℝ}
    (hσ : (σ.toBilinForm - σ.toBilinForm.flip).Nondegenerate) {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (e : V x ≃L[ℝ] W) :
    g.polarFormulaAt x σ = e.symm.conjContinuousAlgEquiv (TauCeti.metricPolarFormula
      (e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (g.inner x))
      (e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) σ)) := by
  let e₀ := euclideanEquivAt F V x
  -- Carrying along `e` is carrying along `e₀`, then along `f = e₀⁻¹ ≫ e`.
  let f := e₀.symm.trans e
  have hc (τ : V x →L[ℝ] V x →L[ℝ] ℝ) :
      e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) τ =
        (e₀.arrowCongr (e₀.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) τ).bilinearComp
          (f.symm : W →L[ℝ] _) (f.symm : W →L[ℝ] _) := by
    ext v w
    simp [f]
  rw [polarFormulaAt_def, hc, hc,
    TauCeti.metricPolarFormula_conj f (g.mem_polarDomain_arrowCongr e₀ hσ)]
  ext v
  simp [f, e₀]

/-- For a metric of class `Cⁿ`, the polar formula is a `Cⁿ` map from the bundle of bilinear forms
to the endomorphism bundle on the domain `Bundle.polarFormulaDomain F V`. -/
theorem contMDiffOn_polarFormulaAt :
    ContMDiffOn (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun q : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) ↦
        TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) q.proj
          (g.polarFormulaAt q.proj q.snd))
      (polarFormulaDomain F V) := by
  intro q₀ hq₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_proj _, ?_⟩
  set x₀ := q₀.proj
  let e₀ := trivializationAt F V x₀
  let W := EuclideanSpace ℝ (Fin (finrank ℝ F))
  let T : F ≃L[ℝ] W := .ofFinrankEq finrank_euclideanSpace_fin.symm
  let Ts : W →L[ℝ] F := T.symm
  let pull : (F →L[ℝ] ℝ) →L[ℝ] W →L[ℝ] ℝ := (ContinuousLinearMap.compL ℝ W F ℝ).flip Ts
  -- The readings of the metric and of the form in the trivialization at `x₀`, carried to `W`.
  let gC (q : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ)) :=
    ContinuousLinearMap.inCoordinates F V (F →L[ℝ] ℝ) (fun y ↦ V y →L[ℝ] Trivial M ℝ y)
      x₀ q.proj x₀ q.proj (g.inner q.proj)
  let sC (q : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ)) :=
    ContinuousLinearMap.inCoordinates F V (F →L[ℝ] ℝ) (fun y ↦ V y →L[ℝ] Trivial M ℝ y)
      x₀ q.proj x₀ q.proj q.snd
  have hgC : ContMDiffAt (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) n gC q₀ :=
    g.contMDiffAt_inCoordinates_inner (f := TotalSpace.proj) (contMDiffAt_proj _)
  have hsC : ContMDiffAt (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) n sC q₀ :=
    ((contMDiffAt_hom_bundle (fun q ↦ q)).1 contMDiffAt_id).2
  let G q := pull.comp ((gC q).comp Ts)
  let S q := pull.comp ((sC q).comp Ts)
  -- Over the base set, `G` and `S` are the metric and the form carried along `E q`.
  let E (q : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ))
      (hq : q.proj ∈ e₀.baseSet) : V q.proj ≃L[ℝ] W :=
    (e₀.continuousLinearEquivAt ℝ q.proj hq).trans T
  have hC (q) (hq : q.proj ∈ e₀.baseSet) (τ : V q.proj →L[ℝ] V q.proj →L[ℝ] ℝ) :
      pull.comp ((ContinuousLinearMap.inCoordinates F V (F →L[ℝ] ℝ)
        (fun y ↦ V y →L[ℝ] Trivial M ℝ y) x₀ q.proj x₀ q.proj τ).comp Ts) =
      (E q hq).arrowCongr ((E q hq).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) τ := by
    ext v w
    simp [pull, Ts, E, e₀, ContinuousLinearMap.inCoordinates_eq_arrowCongr_arrowCongr hq]
  have hU : {q | q.proj ∈ e₀.baseSet} ∩ polarFormulaDomain F V ∈ 𝓝 q₀ :=
    inter_mem ((FiberBundle.continuous_proj _ _).continuousAt.preimage_mem_nhds
      (e₀.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x₀)))
      (isOpen_polarFormulaDomain.mem_nhds hq₀)
  have hmem (q) (hq : q ∈ {q | q.proj ∈ e₀.baseSet} ∩ polarFormulaDomain F V) :
      (G q, S q) ∈ TauCeti.polarDomain W := by
    simp only [G, S, gC, sC, hC q hq.1]
    exact g.mem_polarDomain_arrowCongr _ hq.2
  have hGS : ContMDiffAt (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ))
      𝓘(ℝ, (W →L[ℝ] W →L[ℝ] ℝ) × (W →L[ℝ] W →L[ℝ] ℝ)) n (fun q ↦ (G q, S q)) q₀ :=
    (contMDiffAt_const.clm_comp (hgC.clm_comp contMDiffAt_const)).prodMk_space
      (contMDiffAt_const.clm_comp (hsC.clm_comp contMDiffAt_const))
  have hP := ContDiffAt.comp_contMDiffAt (f := fun q ↦ (G q, S q)) (x := q₀)
    (TauCeti.contDiffOn_metricPolarFormula.contDiffAt
      ((TauCeti.isOpen_polarDomain W).mem_nhds (hmem q₀ (mem_of_mem_nhds hU)))) hGS
  refine ((contMDiffAt_const (c := Ts)).clm_comp (hP.clm_comp
    (contMDiffAt_const (c := (T : F →L[ℝ] W))))).congr_of_eventuallyEq ?_
  filter_upwards [hU] with q hq
  rw [ContinuousLinearMap.inCoordinates_eq_conjContinuousAlgEquiv hq.1,
    g.polarFormulaAt_eq_conj hq.2 (E q hq.1), ← hC q hq.1, ← hC q hq.1]
  ext v
  simp [E, Ts, e₀, G, S, gC, sC, Trivialization.apply_mk_symm _ hq.1]

end ContMDiffRiemannianMetric

/-! ### The polar formula on the endomorphism bundle -/

namespace ContMDiffRiemannianMetric

variable {n : WithTop ℕ∞} (g : ContMDiffRiemannianMetric I n F V)

/-- The continuous bilinear form `(u, v) ↦ (g(B u, v) - g(u, B v)) / 2` on the fibre `V x`, for a
bundle metric `g` and an endomorphism `B` of `V x`. -/
def compatibleBilinAt (x : M) (B : V x →L[ℝ] V x) : V x →L[ℝ] V x →L[ℝ] ℝ :=
  (2 : ℝ)⁻¹ • ((g.inner x).comp B - (ContinuousLinearMap.precomp ℝ B).comp (g.inner x))

theorem compatibleBilinAt_def (x : M) (B : V x →L[ℝ] V x) :
    g.compatibleBilinAt x B =
      (2 : ℝ)⁻¹ • ((g.inner x).comp B - (ContinuousLinearMap.precomp ℝ B).comp (g.inner x)) :=
  (rfl)

@[simp]
theorem compatibleBilinAt_apply (x : M) (B : V x →L[ℝ] V x) (u v : V x) :
    g.compatibleBilinAt x B u v = (2 : ℝ)⁻¹ * (g.inner x (B u) v - g.inner x u (B v)) := by
  simp [compatibleBilinAt_def]

/-- The form `compatibleBilinAt g x B` is alternating. -/
theorem isAlt_compatibleBilinAt (x : M) (B : V x →L[ℝ] V x) :
    (g.compatibleBilinAt x B).toBilinForm.IsAlt := fun u ↦ by
  simp [g.symm x (B u) u]

theorem compatibleBilinAt_add [∀ x, ContinuousAdd (V x)] (x : M) (B C : V x →L[ℝ] V x) :
    g.compatibleBilinAt x (B + C) = g.compatibleBilinAt x B + g.compatibleBilinAt x C := by
  ext u v
  simp only [compatibleBilinAt_apply, add_apply, map_add]
  ring

theorem compatibleBilinAt_smul [∀ x, ContinuousConstSMul ℝ (V x)] (x : M) (c : ℝ)
    (B : V x →L[ℝ] V x) :
    g.compatibleBilinAt x (c • B) = c • g.compatibleBilinAt x B := by
  ext u v
  simp only [compatibleBilinAt_apply, smul_apply, map_smul, smul_eq_mul]
  ring

/-- For a metric of class `Cⁿ`, the map `(x, B) ↦ (x, compatibleBilinAt g x B)` from the
endomorphism bundle to the bundle of bilinear forms is `Cⁿ`. -/
theorem contMDiff_compatibleBilinAt [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul ℝ (V x)] :
    ContMDiff (I.prod 𝓘(ℝ, F →L[ℝ] F)) (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun q : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x) ↦
        TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) (E := fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) q.proj
          (g.compatibleBilinAt q.proj q.snd)) := by
  intro q₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_proj _, ?_⟩
  set x₀ := q₀.proj
  let e₀ := trivializationAt F V x₀
  -- The readings of the metric and of the endomorphism in the trivialization at `x₀`.
  let gC (q : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)) :=
    ContinuousLinearMap.inCoordinates F V (F →L[ℝ] ℝ) (fun y ↦ V y →L[ℝ] Trivial M ℝ y)
      x₀ q.proj x₀ q.proj (g.inner q.proj)
  let bC (q : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)) :=
    ContinuousLinearMap.inCoordinates F V F V x₀ q.proj x₀ q.proj q.snd
  have hgC : ContMDiffAt (I.prod 𝓘(ℝ, F →L[ℝ] F)) 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) n gC q₀ :=
    g.contMDiffAt_inCoordinates_inner (f := TotalSpace.proj) (contMDiffAt_proj _)
  have hbC : ContMDiffAt (I.prod 𝓘(ℝ, F →L[ℝ] F)) 𝓘(ℝ, F →L[ℝ] F) n bC q₀ :=
    ((contMDiffAt_hom_bundle (fun q ↦ q)).1 contMDiffAt_id).2
  have hd : ContDiff ℝ n fun p : (F →L[ℝ] F →L[ℝ] ℝ) × (F →L[ℝ] F →L[ℝ] ℝ) ↦
      (2 : ℝ)⁻¹ • (p.1 - p.2) :=
    (contDiff_fst.sub contDiff_snd).const_smul _
  refine (hd.comp_contMDiffAt ((hgC.clm_comp hbC).prodMk_space
    (hbC.clm_precomp.clm_comp hgC))).congr_of_eventuallyEq ?_
  filter_upwards [(FiberBundle.continuous_proj _ _).continuousAt.preimage_mem_nhds
    (e₀.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x₀))] with q hq
  ext u v
  simp [gC, bC, e₀, ContinuousLinearMap.inCoordinates_eq_arrowCongr_arrowCongr hq,
    ContinuousLinearMap.inCoordinates_eq_conjContinuousAlgEquiv hq,
    Trivialization.symm_apply_apply_mk _ hq]

/-- The points `(x, B)` of the endomorphism bundle at which the form `compatibleBilinAt g x B` is
nondegenerate: the preimage of `Bundle.polarFormulaDomain F V` under `compatibleBilinAt g`. -/
def polarEndDomain : Set (TotalSpace (F →L[ℝ] F) fun x ↦ V x →L[ℝ] V x) :=
  {q | (⟨q.proj, g.compatibleBilinAt q.proj q.snd⟩ :
    TotalSpace (F →L[ℝ] F →L[ℝ] ℝ) fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) ∈ polarFormulaDomain F V}

@[simp]
theorem mem_polarEndDomain_iff {q : TotalSpace (F →L[ℝ] F) fun x ↦ V x →L[ℝ] V x} :
    q ∈ g.polarEndDomain ↔
      ((g.compatibleBilinAt q.proj q.snd).toBilinForm -
        (g.compatibleBilinAt q.proj q.snd).toBilinForm.flip).Nondegenerate :=
  Iff.rfl

/-- In finite rank, the set `polarEndDomain g` is open in the endomorphism bundle. -/
theorem isOpen_polarEndDomain [FiniteDimensional ℝ F] [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul ℝ (V x)] : IsOpen g.polarEndDomain :=
  isOpen_polarFormulaDomain.preimage g.contMDiff_compatibleBilinAt.continuous

variable [FiniteDimensional ℝ F] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

/-- The endomorphism `J_{g,ω_{g,B}}` of the fibre `V x`, for an endomorphism `B` of `V x`: the
polar formula `polarFormulaAt g x` at the form `compatibleBilinAt g x B`. -/
def polarEndAt (x : M) (B : V x →L[ℝ] V x) : V x →L[ℝ] V x :=
  g.polarFormulaAt x (g.compatibleBilinAt x B)

theorem polarEndAt_def (x : M) (B : V x →L[ℝ] V x) :
    g.polarEndAt x B = g.polarFormulaAt x (g.compatibleBilinAt x B) :=
  (rfl)

/-- For a metric of class `Cⁿ`, the map `(x, B) ↦ (x, polarEndAt g x B)` of the endomorphism
bundle to itself is `Cⁿ` on `polarEndDomain g`. -/
theorem contMDiffOn_polarEndAt :
    ContMDiffOn (I.prod 𝓘(ℝ, F →L[ℝ] F)) (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun q : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x) ↦
        TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) q.proj
          (g.polarEndAt q.proj q.snd))
      g.polarEndDomain := by
  simp only [polarEndAt_def]
  exact g.contMDiffOn_polarFormulaAt.comp g.contMDiff_compatibleBilinAt.contMDiffOn
    fun _ hq ↦ hq

end ContMDiffRiemannianMetric

end Bundle
