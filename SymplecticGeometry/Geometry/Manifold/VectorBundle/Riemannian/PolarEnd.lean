/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import SymplecticGeometry.Analysis.InnerProductSpace.Symplectic.PolarComplexStructure.Smooth
public import TauCeti.Topology.VectorBundle.Coordinates

/-!
# The polar formula on the bundle of bilinear forms

Let `g` be a bundle metric on a real vector bundle `V → M` of finite rank. For a continuous
bilinear form `σ` on a fibre `V x` whose skew part is nondegenerate, this file defines the
endomorphism `J_{g,σ}` of `V x` (`Bundle.ContMDiffRiemannianMetric.polarFormulaAt g x σ`): the
formula `TauCeti.metricPolarFormula` applied to the pair `(g x, σ)`, read on a Euclidean space
through a linear equivalence of `V x` with it. It shows that this does not depend on the
equivalence, and that it is a `Cⁿ` map from the bundle of bilinear forms to the endomorphism bundle
on the open set where it is defined. At the flat map of a nondegenerate two-form it is the
complex structure `J_{g,ω}` of the bundle, which is built from it in
`SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic`.

## Main definitions

* `Bundle.polarFormulaDomain F V`: the points `(x, σ)` of the bundle of bilinear forms where the
  skew part of `σ` is nondegenerate.
* `Bundle.ContMDiffRiemannianMetric.polarFormulaAt g x σ`: the endomorphism `J_{g,σ}` of `V x`.

## Main results

* `Bundle.isOpen_polarFormulaDomain`: in finite rank, the domain is open.
* `Bundle.ContMDiffRiemannianMetric.polarFormulaAt_eq_conj`: on the domain, `J_{g,σ}` is the
  formula read through any linear equivalence of `V x` with a finite-dimensional inner product
  space.
* `Bundle.ContMDiffRiemannianMetric.contMDiffOn_polarFormulaAt`: for a metric of class `Cⁿ`, the
  map `(x, σ) ↦ (x, J_{g,σ})` is `Cⁿ` on the domain.
* `Bundle.ContMDiffRiemannianMetric.exists_continuousLinearEquiv_inner_eq`: each fibre of a
  bundle metric of finite rank is isometric to a Euclidean space.

## Implementation notes

The fibres of `V` carry no norm, so the formula, which needs an inner product space, is applied on
the Euclidean space `EuclideanSpace ℝ (Fin (finrank ℝ F))`, reached from `V x` through the
trivialization at `x`. The proof of `contMDiffOn_polarFormulaAt` adapts that of Tau Ceti's private
`TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_polarEnd`
(`TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/Polar.lean`): it reads the map in the
trivialization at a base point, where it becomes the formula at the coordinate readings of the
metric and of the form, conjugated by a constant equivalence. Here the form is a coordinate of the
total space instead of a fixed section, and the formula is smooth by
`TauCeti.contDiffOn_metricPolarFormula`. The openness proof follows that of
`SymplecticGeometry.Bundle.isOpen_setOf_nondegenerate`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.5.6
-/

public section

noncomputable section

open Module Set Filter
open scoped Manifold Topology RealInnerProductSpace

/-- Carrying a continuous bilinear form along a continuous linear equivalence `e` does not change
whether its skew part `σ - σᵀ` is nondegenerate. -/
theorem ContinuousLinearEquiv.nondegenerate_arrowCongr_sub_flip_iff {X W : Type*}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℝ X] [NormedAddCommGroup W] [NormedSpace ℝ W] (e : X ≃L[ℝ] W)
    {σ : X →L[ℝ] X →L[ℝ] ℝ} :
    (e.arrowCongr (e.arrowCongr (.refl ℝ ℝ)) σ -
        (e.arrowCongr (e.arrowCongr (.refl ℝ ℝ)) σ).flip).toBilinForm.Nondegenerate ↔
      (σ.toBilinForm - σ.toBilinForm.flip).Nondegenerate := by
  have h : (e.arrowCongr (e.arrowCongr (.refl ℝ ℝ)) σ -
        (e.arrowCongr (e.arrowCongr (.refl ℝ ℝ)) σ).flip).toBilinForm =
      LinearMap.BilinForm.congr e.toLinearEquiv (σ.toBilinForm - σ.toBilinForm.flip) := by
    ext v w
    simp
  rw [h, LinearMap.BilinForm.nondegenerate_congr_iff]

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
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- A continuous bilinear form on `V x`, read in the trivialization at `x₀` whose base set
contains `x`, is the form carried along the fibre equivalence of that trivialization. -/
theorem _root_.ContinuousLinearMap.inCoordinates_eq_arrowCongr_arrowCongr {x₀ x : M}
    (hx : x ∈ (trivializationAt F V x₀).baseSet) (σ : V x →L[ℝ] V x →L[ℝ] ℝ) :
    ContinuousLinearMap.inCoordinates F V (F →L[ℝ] ℝ) (fun y ↦ V y →L[ℝ] Trivial M ℝ y)
        x₀ x x₀ x σ =
      ((trivializationAt F V x₀).continuousLinearEquivAt ℝ x hx).arrowCongr
        (((trivializationAt F V x₀).continuousLinearEquivAt ℝ x hx).arrowCongr
          (.refl ℝ ℝ)) σ := by
  ext v w
  rw [inCoordinates_apply_eq₂ (E₃ := Trivial M ℝ) hx hx (Set.mem_univ _)]
  simp

/-- In finite rank, the domain of the polar formula is open in the bundle of bilinear forms. -/
theorem isOpen_polarFormulaDomain [FiniteDimensional ℝ F] :
    IsOpen (polarFormulaDomain F V) := by
  rw [isOpen_iff_mem_nhds]
  intro q₀ hq₀
  let e := trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) q₀.proj
  have hT : IsOpen {s : F →L[ℝ] F →L[ℝ] ℝ | (s - s.flip).toBilinForm.Nondegenerate} :=
    ContinuousLinearMap.isOpen_setOf_nondegenerate_toBilinForm.preimage
      (continuous_id.sub (ContinuousLinearMap.flipₗᵢ ℝ F F ℝ).continuous)
  -- In the fibre coordinates of `e`, a form becomes its carrying along a linear equivalence.
  have key : ∀ q ∈ e.source,
      (q ∈ polarFormulaDomain F V ↔ ((e q).2 - (e q).2.flip).toBilinForm.Nondegenerate) := by
    intro q hq
    have hy : q.proj ∈ (trivializationAt F V q₀.proj).baseSet := by
      simpa [e] using hq
    rw [mem_polarFormulaDomain_iff, hom_trivializationAt_apply,
      ContinuousLinearMap.inCoordinates_eq_arrowCongr_arrowCongr hy,
      ContinuousLinearEquiv.nondegenerate_arrowCongr_sub_flip_iff]
  have hU := e.continuousOn.isOpen_inter_preimage e.open_source (hT.preimage continuous_snd)
  have hq₀e : q₀ ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
  refine Filter.mem_of_superset (hU.mem_nhds ⟨hq₀e, (key q₀ hq₀e).1 hq₀⟩) ?_
  rintro q ⟨hq, hq'⟩
  exact (key q hq).2 hq'

/-! ### The polar formula on a fibre -/

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

namespace ContMDiffRiemannianMetric

variable [FiniteDimensional ℝ F] {n : WithTop ℕ∞} (g : ContMDiffRiemannianMetric I n F V)

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
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


/-- The polar formula `J_{g,σ}` of a bundle metric `g` and a continuous bilinear form `σ` on the
fibre `V x`: the formula `TauCeti.metricPolarFormula` of the pair `(g x, σ)`, carried to the
Euclidean space `EuclideanSpace ℝ (Fin (finrank ℝ F))` along the trivialization at `x` and
conjugated back.
Where the skew part of `σ` is nondegenerate, the choice of the equivalence does not matter
(`polarFormulaAt_eq_conj`). -/
def polarFormulaAt (x : M) (σ : V x →L[ℝ] V x →L[ℝ] ℝ) : V x →L[ℝ] V x :=
  let e : V x ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ F)) :=
    ((trivializationAt F V x).continuousLinearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x)).trans
      (.ofFinrankEq finrank_euclideanSpace_fin.symm)
  e.symm.conjContinuousAlgEquiv (TauCeti.metricPolarFormula
    (e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (g.inner x))
    (e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) σ))

theorem polarFormulaAt_def (x : M) (σ : V x →L[ℝ] V x →L[ℝ] ℝ) :
    g.polarFormulaAt x σ =
      let e : V x ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ F)) :=
        ((trivializationAt F V x).continuousLinearEquivAt ℝ x
          (FiberBundle.mem_baseSet_trivializationAt' x)).trans
          (.ofFinrankEq finrank_euclideanSpace_fin.symm)
      e.symm.conjContinuousAlgEquiv (TauCeti.metricPolarFormula
        (e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (g.inner x))
        (e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) σ)) :=
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
  let e₀ : V x ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ F)) :=
    ((trivializationAt F V x).continuousLinearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x)).trans
      (.ofFinrankEq finrank_euclideanSpace_fin.symm)
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
    ((contMDiffAt_hom_bundle (fun q : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
      (fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) q.proj (g.inner q.proj))).1
      ((g.contMDiff q₀.proj).comp q₀ (contMDiffAt_proj _))).2
  have hsC : ContMDiffAt (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) n sC q₀ :=
    ((contMDiffAt_hom_bundle (fun q ↦ q)).1 contMDiffAt_id).2
  let G q := pull.comp ((gC q).comp Ts)
  let S q := pull.comp ((sC q).comp Ts)
  -- Over the base set, `G` and `S` are the metric and the form carried along `E q`.
  let E (q : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ))
      (hq : q.proj ∈ e₀.baseSet) : V q.proj ≃L[ℝ] W :=
    (e₀.continuousLinearEquivAt ℝ q.proj hq).trans T
  have hG (q) (hq : q.proj ∈ e₀.baseSet) : G q =
      (E q hq).arrowCongr ((E q hq).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
        (g.inner q.proj) := by
    ext v w
    simp [G, gC, pull, Ts, E, e₀, ContinuousLinearMap.inCoordinates_eq_arrowCongr_arrowCongr hq]
  have hS (q) (hq : q.proj ∈ e₀.baseSet) : S q =
      (E q hq).arrowCongr ((E q hq).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) q.snd := by
    ext v w
    simp [S, sC, pull, Ts, E, e₀, ContinuousLinearMap.inCoordinates_eq_arrowCongr_arrowCongr hq]
  have hU : {q | q.proj ∈ e₀.baseSet} ∩ polarFormulaDomain F V ∈ 𝓝 q₀ :=
    inter_mem ((FiberBundle.continuous_proj _ _).continuousAt.preimage_mem_nhds
      (e₀.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x₀)))
      (isOpen_polarFormulaDomain.mem_nhds hq₀)
  have hmem (q) (hq : q ∈ {q | q.proj ∈ e₀.baseSet} ∩ polarFormulaDomain F V) :
      (G q, S q) ∈ TauCeti.polarDomain W := by
    rw [hG q hq.1, hS q hq.1]
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
    g.polarFormulaAt_eq_conj hq.2 (E q hq.1),
    ← hG q hq.1, ← hS q hq.1]
  ext v
  simp [E, Ts, e₀, Trivialization.apply_mk_symm _ hq.1]

end ContMDiffRiemannianMetric

end Bundle
