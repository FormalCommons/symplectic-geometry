/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Coordinates
public import SymplecticGeometry.Topology.Algebra.Module.BilinearForm
import SymplecticGeometry.Topology.VectorBundle.Coordinates
import SymplecticGeometry.Topology.FiberBundle.Basic

/-!
# Natural maps on pairs of bilinear forms, applied in the fibres of a vector bundle

Let `W` be a normed space and `Φ` a map that sends a pair of continuous bilinear forms on `W` to
an endomorphism of `W`. Given a family `e x : V x ≃L[ℝ] W` of continuous linear equivalences of
the fibres of a real vector bundle `V` with `W`, this file defines the endomorphism of `V x`
obtained from `Φ` and a pair `(a, b)` of continuous bilinear forms on `V x`: carry `a` and `b` to
`W` along `e x`, apply `Φ`, and conjugate back
(`SymplecticGeometry.Bundle.mapBilinPairAt e Φ x a b`).

Let `Φ'` be a map of the same kind on another normed space `W'`, related to `Φ` on a set `U'` of
pairs on `W'`: for every continuous linear equivalence `f : W' ≃L[ℝ] W` and `p ∈ U'`, carrying
both forms of `p` along `f` and applying `Φ` gives `Φ' p` conjugated by `f`. Then the endomorphism
may be computed from `Φ'` through any equivalence of `V x` with `W'` that carries the pair into
`U'` (`mapBilinPairAt_eq_conj`). With `W' = W` and `Φ' = Φ`: if `Φ` is natural on a set `U` under
the automorphisms of `W`, the endomorphism does not depend on the equivalence. If moreover `U` is
open and `Φ` is `Cⁿ` on `U`, then applying the construction to two sections of the bundle of
bilinear forms along a map, both `Cⁿ` at a point where their carried pair lies in `U`, gives a
section of the endomorphism bundle along that map that is `Cⁿ` at that point
(`contMDiffAt_mapBilinPairAt`).

## Main definitions

* `SymplecticGeometry.Bundle.mapBilinPairAt e Φ x a b`: the endomorphism
  `(e x)⁻¹ ∘ Φ (a, b) ∘ e x` of `V x`, with `a` and `b` carried to `W` along `e x`.

## Main results

* `SymplecticGeometry.Bundle.mapBilinPairAt_eq_conj`: for `Φ` related to `Φ'` on `U'` by the
  equivalences `W' ≃L[ℝ] W`, the endomorphism may be computed from `Φ'` through any continuous
  linear equivalence of `V x` with `W'` that carries the pair into `U'`.
* `SymplecticGeometry.Bundle.contMDiffAt_mapBilinPairAt`: for `Φ` natural and `Cⁿ` on an open
  set `U`, the construction is `Cⁿ` along sections that are `Cⁿ` at a point where their pair
  is carried into `U`.

## Implementation notes

The smoothness proof reads the section in the trivialization at the base point `x₀`. Near `x₀`,
by `mapBilinPairAt_eq_conj` with the fibre equivalence of that trivialization, the reading is
`Φ` at the coordinate readings of the two forms, conjugated by a constant equivalence of the
model fibre with `W`; it is then `Cⁿ` since `Φ` is. This is the argument of the proof of Tau
Ceti's private `TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_polarEnd`
(`TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/Polar.lean`), with any natural map in place
of the polar formula and sections along a map in place of a fixed section.
-/

public section

noncomputable section

open _root_.Bundle Set Filter
open scoped Manifold Topology

namespace SymplecticGeometry.Bundle

variable {M : Type*} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]

/-- The endomorphism of the fibre `V x` given by a map `Φ` from pairs of continuous bilinear forms
on `W` to endomorphisms of `W`, read through the equivalence `e x : V x ≃L[ℝ] W`: the pair
`(a, b)` is carried to `W` along `e x`, and `Φ` of the result is conjugated back to `V x`. -/
def mapBilinPairAt (e : ∀ x, V x ≃L[ℝ] W)
    (Φ : (W →L[ℝ] W →L[ℝ] ℝ) × (W →L[ℝ] W →L[ℝ] ℝ) → W →L[ℝ] W) (x : M)
    (a b : V x →L[ℝ] V x →L[ℝ] ℝ) : V x →L[ℝ] V x :=
  (e x).symm.conjContinuousAlgEquiv (Φ ((e x).bilinearCongr a, (e x).bilinearCongr b))

theorem mapBilinPairAt_def (e : ∀ x, V x ≃L[ℝ] W)
    (Φ : (W →L[ℝ] W →L[ℝ] ℝ) × (W →L[ℝ] W →L[ℝ] ℝ) → W →L[ℝ] W) (x : M)
    (a b : V x →L[ℝ] V x →L[ℝ] ℝ) :
    mapBilinPairAt e Φ x a b =
      (e x).symm.conjContinuousAlgEquiv (Φ ((e x).bilinearCongr a, (e x).bilinearCongr b)) :=
  (rfl)

variable {Φ : (W →L[ℝ] W →L[ℝ] ℝ) × (W →L[ℝ] W →L[ℝ] ℝ) → W →L[ℝ] W}
  {U : Set ((W →L[ℝ] W →L[ℝ] ℝ) × (W →L[ℝ] W →L[ℝ] ℝ))}

/-- **Independence of the equivalence.** Let `Φ'` send pairs of continuous bilinear forms on a
normed space `W'` to endomorphisms of `W'`, so that for every continuous linear equivalence
`f : W' ≃L[ℝ] W` and every pair `p ∈ U'`, `Φ` of `p` carried along `f` is `Φ' p` conjugated by
`f`. Then for any continuous linear equivalence `e'` of `V x` with `W'` that carries `(a, b)` into
`U'`, `mapBilinPairAt e Φ x a b` is `Φ'` of `(a, b)` carried along `e'`, conjugated back by
`e'`. -/
theorem mapBilinPairAt_eq_conj (e : ∀ x, V x ≃L[ℝ] W) {W' : Type*} [NormedAddCommGroup W']
    [NormedSpace ℝ W'] {Φ' : (W' →L[ℝ] W' →L[ℝ] ℝ) × (W' →L[ℝ] W' →L[ℝ] ℝ) → W' →L[ℝ] W'}
    {U' : Set ((W' →L[ℝ] W' →L[ℝ] ℝ) × (W' →L[ℝ] W' →L[ℝ] ℝ))}
    (hΦ : ∀ f : W' ≃L[ℝ] W, ∀ p ∈ U',
      Φ (f.bilinearCongr p.1, f.bilinearCongr p.2) = f.conjContinuousAlgEquiv (Φ' p))
    {x : M} {a b : V x →L[ℝ] V x →L[ℝ] ℝ} (e' : V x ≃L[ℝ] W')
    (h : (e'.bilinearCongr a, e'.bilinearCongr b) ∈ U') :
    mapBilinPairAt e Φ x a b =
      e'.symm.conjContinuousAlgEquiv (Φ' (e'.bilinearCongr a, e'.bilinearCongr b)) := by
  -- `e x` is `e'` followed by the equivalence `f : W' ≃L[ℝ] W`.
  let f := e'.symm.trans (e x)
  have he : e x = e'.trans f := by
    ext v
    simp [f]
  rw [mapBilinPairAt_def, he, ContinuousLinearEquiv.bilinearCongr_trans,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply, hΦ f _ h]
  ext v
  simp

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {I : ModelWithCorners ℝ EB HB} [TopologicalSpace M] [ChartedSpace HB M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]

/-- **Smoothness.** Let `Φ` be natural under the automorphisms of `W` and `Cⁿ` on an open set
`U`. Along a map `f : N → M`, let `a` and `b` be sections of the bundle of continuous bilinear
forms that are `Cⁿ` at `y₀`, and suppose that `(a y₀, b y₀)`, carried along `e (f y₀)`, lies in
`U`. Then `y ↦ mapBilinPairAt e Φ (f y) (a y) (b y)` is a section of the endomorphism bundle along
`f` that is `Cⁿ` at `y₀`. -/
theorem contMDiffAt_mapBilinPairAt {n : WithTop ℕ∞} (e : ∀ x, V x ≃L[ℝ] W) (hU : IsOpen U)
    (hΦd : ContDiffOn ℝ n Φ U)
    (hΦ : ∀ f : W ≃L[ℝ] W, ∀ p ∈ U,
      Φ (f.bilinearCongr p.1, f.bilinearCongr p.2) = f.conjContinuousAlgEquiv (Φ p))
    {f : N → M} {a b : ∀ y, V (f y) →L[ℝ] V (f y) →L[ℝ] ℝ} {y₀ : N}
    (ha : ContMDiffAt IN (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n (fun y ↦
      TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) (E := fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) (f y) (a y)) y₀)
    (hb : ContMDiffAt IN (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n (fun y ↦
      TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) (E := fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) (f y) (b y)) y₀)
    (h₀ : ((e (f y₀)).bilinearCongr (a y₀), (e (f y₀)).bilinearCongr (b y₀)) ∈ U) :
    ContMDiffAt IN (I.prod 𝓘(ℝ, F →L[ℝ] F)) n (fun y ↦
      TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) (f y)
        (mapBilinPairAt e Φ (f y) (a y) (b y))) y₀ := by
  have hf : ContMDiffAt IN I n f y₀ := ((contMDiffAt_hom_bundle _).1 ha).1
  rw [contMDiffAt_hom_bundle]
  refine ⟨hf, ?_⟩
  set x₀ := f y₀
  let e₀ := trivializationAt F V x₀
  have hx₀ : x₀ ∈ e₀.baseSet := mem_baseSet_trivializationAt F V x₀
  -- The constant equivalence of the model fibre with `W` at `x₀`.
  let T : F ≃L[ℝ] W := (e₀.continuousLinearEquivAt ℝ x₀ hx₀).symm.trans (e x₀)
  -- The readings of the two forms in the trivialization at `x₀`, carried to `W` along `T`.
  let C (σ : ∀ y, V (f y) →L[ℝ] V (f y) →L[ℝ] ℝ) (y : N) : W →L[ℝ] W →L[ℝ] ℝ :=
    T.bilinearCongr (ContinuousLinearMap.inCoordinates F V (F →L[ℝ] ℝ)
      (fun x ↦ V x →L[ℝ] Trivial M ℝ x) x₀ (f y) x₀ (f y) (σ y))
  have hC (σ : ∀ y, V (f y) →L[ℝ] V (f y) →L[ℝ] ℝ)
      (hσ : ContMDiffAt IN (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n (fun y ↦
        TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) (E := fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) (f y) (σ y))
        y₀) :
      ContMDiffAt IN 𝓘(ℝ, W →L[ℝ] W →L[ℝ] ℝ) n (C σ) y₀ := by
    have hR : ContMDiffAt IN 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) n
        (fun y ↦ ContinuousLinearMap.inCoordinates F V (F →L[ℝ] ℝ)
          (fun x ↦ V x →L[ℝ] Trivial M ℝ x) x₀ (f y) x₀ (f y) (σ y)) y₀ :=
      ((contMDiffAt_hom_bundle _).1 hσ).2
    -- Carrying along `T` is a continuous linear map, hence smooth.
    have hL : ContDiff ℝ n
        (T.bilinearCongr (G := ℝ) : (F →L[ℝ] F →L[ℝ] ℝ) → W →L[ℝ] W →L[ℝ] ℝ) :=
      ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := F →L[ℝ] F →L[ℝ] ℝ)
        (F := W →L[ℝ] W →L[ℝ] ℝ) (T.bilinearCongr (G := ℝ))
    exact hL.contDiffAt.comp_contMDiffAt hR
  -- Over the base set, the readings are the forms carried along the fibre equivalence and `T`.
  have hcarry (y : N) (hy : f y ∈ e₀.baseSet) (σ : ∀ y, V (f y) →L[ℝ] V (f y) →L[ℝ] ℝ) :
      C σ y = ((e₀.continuousLinearEquivAt ℝ (f y) hy).trans T).bilinearCongr (σ y) := by
    rw [ContinuousLinearEquiv.bilinearCongr_trans, ContinuousLinearEquiv.trans_apply,
      ← ContinuousLinearMap.inCoordinates_eq_bilinearCongr hy]
  have hT : (e₀.continuousLinearEquivAt ℝ x₀ hx₀).trans T = e x₀ := by
    ext v
    simp [T, e₀, Trivialization.symm_apply_apply_mk _ hx₀]
  have hP₀ : (C a y₀, C b y₀) ∈ U := by
    rwa [hcarry y₀ hx₀, hcarry y₀ hx₀, hT]
  have hP := ContDiffAt.comp_contMDiffAt (f := fun y ↦ (C a y, C b y)) (x := y₀)
    (hΦd.contDiffAt (hU.mem_nhds hP₀)) ((hC a ha).prodMk_space (hC b hb))
  have hbase : ∀ᶠ y in 𝓝 y₀, f y ∈ e₀.baseSet :=
    hf.continuousAt.eventually_mem_baseSet_trivializationAt F V
  have hU' : ∀ᶠ y in 𝓝 y₀, (C a y, C b y) ∈ U :=
    ((hC a ha).prodMk_space (hC b hb)).continuousAt.preimage_mem_nhds (hU.mem_nhds hP₀)
  refine ((contMDiffAt_const (c := (T.symm : W →L[ℝ] F))).clm_comp (hP.clm_comp
    (contMDiffAt_const (c := (T : F →L[ℝ] W))))).congr_of_eventuallyEq ?_
  filter_upwards [hbase, hU'] with y hy hyU
  rw [hcarry y hy, hcarry y hy] at hyU
  rw [ContinuousLinearMap.inCoordinates_eq_conjContinuousAlgEquiv hy,
    mapBilinPairAt_eq_conj e hΦ _ hyU, Function.comp_apply, hcarry y hy, hcarry y hy]
  ext v
  simp [e₀, Trivialization.apply_mk_symm _ hy]

end SymplecticGeometry.Bundle

end
