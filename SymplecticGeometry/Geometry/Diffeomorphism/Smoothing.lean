/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Evaluation
public import SymplecticGeometry.Geometry.Diffeomorphism.Sphere.ComplexStructure
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Differential

/-!
# Smoothing families of diffeomorphisms

This file is about continuous families of diffeomorphisms of a compact manifold, for the weak
Whitney topology `Diffeomorph.weakWhitneyTopology` of Tau Ceti.

## Orientation preservation is locally constant

The derivative of a diffeomorphism, read in fixed charts, varies continuously with the
diffeomorphism and the point, and its determinant has no zero. So orientation preservation at a
point is an open condition jointly in the diffeomorphism and the point
(`Diffeomorph.eventually_isOrientationPreservingAt`). On a compact source the tube lemma makes
the diffeomorphisms preserving an orientation everywhere an open set, and the same argument for
orientation reversal makes it closed:

* `Diffeomorph.isClopen_orientationPreservingSubgroup`: `Diffeomorph.orientationPreservingSubgroup`
  is open and closed;
* `SymplecticGeometry.isClopen_diffPlus`: so is `Diff⁺(S²)`, `SymplecticGeometry.diffPlus`.

A clopen set contains the path component of each of its points (Tau Ceti's
`IsClopen.pathComponent_subset`), so a homotopy of maps into the diffeomorphisms that starts in
`diffPlus` stays in `diffPlus` (Tau Ceti's `ContinuousMap.Homotopy.apply_mem`) and is a
homotopy of maps into `diffPlus` (`ContinuousMap.Homotopy.codRestrict`).

The local argument follows Tau Ceti's
`TauCeti.Manifold.Orientation.isLocallyConstant_isOrientationPreservingAt`, which treats a
jointly `C¹` family with a fixed source point: here the family is replaced by a neighbourhood in
the weak Whitney topology, and the source point moves too. The chart differentials are
controlled by Tau Ceti's `TauCeti.tendsto_fderivWithin_extChartAt`.

`TauCeti.Manifold.Orientation.isOrientationPreservingAt_iff_map_eq_of_mem` reads orientation
preservation in the preferred trivializations at any two base points. It generalizes Tau Ceti's
`TauCeti.Manifold.Orientation.isOrientationPreservingAt_iff_map_eq`, whose source trivialization
is the one at the point itself, and its proof follows Tau Ceti's.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Graduate Texts in Mathematics 33,
  Springer, 1976, Chapter 2, §1 (the weak topology).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15.
-/

public section

open Bundle Filter Module Set Topology TauCeti.Manifold

open scoped Manifold ContDiff TauCeti.ComplexManifold TauCeti.DiffeomorphWeakWhitney
  TauCeti.ManifoldWeakWhitney

namespace TauCeti.Manifold.Orientation

variable {E E' H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H]
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N] {ι : Type*} [Fintype ι]

/-- A map `g` preserves the orientations `o` and `o'` at `x` exactly when its derivative `D` at
`x`, read in the preferred trivializations of the tangent bundles at any points `a` and `b` whose
base sets contain `x` and `g x`, carries the orientation of `o` at `x` to that of `o'` at
`g x`, both read in the same trivializations. -/
theorem isOrientationPreservingAt_iff_map_eq_of_mem (o : Orientation I M ι)
    (o' : Orientation J N ι) (g : M → N) {x : M} (a : M) (b : N)
    (D : TangentSpace I x ≃L[ℝ] TangentSpace J (g x))
    (hDc : (D : TangentSpace I x →L[ℝ] TangentSpace J (g x)) = mfderiv I J g x)
    (hx : x ∈ (trivializationAt E (TangentSpace I) a).baseSet)
    (hp : g x ∈ (trivializationAt E' (TangentSpace J) b).baseSet) :
    IsOrientationPreservingAt o o' g x ↔
      _root_.Orientation.map ι
          (((((trivializationAt E (TangentSpace I) a).continuousLinearEquivAt ℝ x hx).symm.trans
            D).trans ((trivializationAt E' (TangentSpace J) b).continuousLinearEquivAt ℝ (g x)
              hp)).toLinearEquiv)
          ((trivializationAt E (TangentSpace I) a).mapOrientation ι hx (o.orientationAt x)) =
        (trivializationAt E' (TangentSpace J) b).mapOrientation ι hp (o'.orientationAt (g x)) := by
  rw [isOrientationPreservingAt_iff_of_coe_eq o o' _ x D hDc]
  have he : ((trivializationAt E (TangentSpace I) a).continuousLinearEquivAt ℝ x hx
      ).toLinearEquiv = (trivializationAt E (TangentSpace I) a).linearEquivAt ℝ x hx := rfl
  have he' : ((trivializationAt E' (TangentSpace J) b).continuousLinearEquivAt ℝ (g x) hp
      ).toLinearEquiv = (trivializationAt E' (TangentSpace J) b).linearEquivAt ℝ (g x) hp := rfl
  simp only [ContinuousLinearEquiv.trans_toLinearEquiv, _root_.Orientation.map_trans,
    Bundle.Trivialization.mapOrientation_apply, ContinuousLinearEquiv.toLinearEquiv_symm, he, he',
    ← _root_.Orientation.map_symm, Equiv.symm_apply_apply]
  exact (_root_.Orientation.map ι _).injective.eq_iff.symm

end TauCeti.Manifold.Orientation

namespace Diffeomorph

open TauCeti.Manifold.Orientation

variable {E E' H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H]
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [CompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N] {ι : Type*} [Fintype ι]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]

/-- **Orientation preservation is open in the diffeomorphism and the point.** If a `C^n`
diffeomorphism `f` of a compact manifold, `n ≠ 0`, preserves the orientations `o` and `o'` at
`x`, then every diffeomorphism near `f` in the weak Whitney topology preserves them at every
point near `x`. -/
theorem eventually_isOrientationPreservingAt (hn : n ≠ 0) {o : Orientation I M ι}
    {o' : Orientation J N ι} {f : M ≃ₘ^n⟮I, J⟯ N} {x : M}
    (h : IsOrientationPreservingAt o o' f x) :
    ∀ᶠ p : (M ≃ₘ^n⟮I, J⟯ N) × M in 𝓝 (f, x), IsOrientationPreservingAt o o' p.1 p.2 := by
  classical
  have hn1 : 1 ≤ n := ENat.one_le_iff_ne_zero_withTop.mpr hn
  set y := f x
  set e := trivializationAt E (TangentSpace I) x
  set e' := trivializationAt E' (TangentSpace J) y
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hy : y ∈ e'.baseSet := FiberBundle.mem_baseSet_trivializationAt' y
  have hev : Continuous fun p : (M ≃ₘ^n⟮I, J⟯ N) × M ↦ p.1 p.2 := continuous_eval
  have hsrc : ∀ᶠ p : (M ≃ₘ^n⟮I, J⟯ N) × M in 𝓝 (f, x), p.2 ∈ e.baseSet :=
    continuous_snd.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hx)
  have htgt : ∀ᶠ p : (M ≃ₘ^n⟮I, J⟯ N) × M in 𝓝 (f, x), p.1 p.2 ∈ e'.baseSet :=
    hev.continuousAt.preimage_mem_nhds (e'.open_baseSet.mem_nhds hy)
  -- The derivative of `p.1` at `p.2`, read in the trivializations at `x` and `y`.
  let T (p : (M ≃ₘ^n⟮I, J⟯ N) × M) (hp : p.2 ∈ e.baseSet) (hq : p.1 p.2 ∈ e'.baseSet) :
      E ≃L[ℝ] E' :=
    ((e.continuousLinearEquivAt ℝ p.2 hp).symm.trans
      (p.1.mfderivToContinuousLinearEquiv hn p.2)).trans
        (e'.continuousLinearEquivAt ℝ (p.1 p.2) hq)
  -- The same derivative as a chart differential, which varies continuously with `p`.
  let c (p : (M ≃ₘ^n⟮I, J⟯ N) × M) : E →L[ℝ] E' :=
    fderivWithin ℝ (extChartAt J y ∘ p.1 ∘ (extChartAt I x).symm) (extChartAt I x).target
      (extChartAt I x p.2)
  have hcT (p : (M ≃ₘ^n⟮I, J⟯ N) × M) (hp : p.2 ∈ e.baseSet) (hq : p.1 p.2 ∈ e'.baseSet) :
      c p = (T p hp hq : E →L[ℝ] E') := by
    have hp' : p.2 ∈ (chartAt H x).source := by
      rwa [← TangentBundle.trivializationAt_baseSet (I := I) x]
    have hq' : p.1 p.2 ∈ (chartAt H' y).source := by
      rwa [← TangentBundle.trivializationAt_baseSet (I := J) y]
    have hp'' : p.2 ∈ (extChartAt I x).source := by rwa [extChartAt_source]
    have h₁ : ((e.continuousLinearEquivAt ℝ p.2 hp).symm : E →L[ℝ] TangentSpace I p.2) =
        tangentCoordChange I x p.2 p.2 := by
      rw [Bundle.Trivialization.symm_continuousLinearEquivAt_eq',
        TangentBundle.symmL_trivializationAt_eq_core hp']
    have h₂ : (e'.continuousLinearEquivAt ℝ (p.1 p.2) hq : TangentSpace J (p.1 p.2) →L[ℝ] E') =
        tangentCoordChange J (p.1 p.2) y (p.1 p.2) := by
      rw [Bundle.Trivialization.coe_continuousLinearEquivAt_eq',
        TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hq']
    simp only [c, T]
    rw [fderivWithin_congr_set (extChartAt_target_eventuallyEqSet_of_mem
        ((extChartAt I x).map_source hp'')),
      p.1.continuous.continuousAt.fderivWithin_extChartAt_comp_extChartAt_symm hp''
        (by rwa [extChartAt_source])]
    ext v
    have h₃ := DFunLike.congr_fun (p.1.mfderivToContinuousLinearEquiv_coe hn (x := p.2))
    simp only [ContinuousLinearEquiv.coe_coe] at h₃
    simp only [ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.trans_apply, h₃, ← h₁, ← h₂]
    -- What is left is `ContinuousLinearMap.comp_apply`, which `rw` cannot use: the composite
    -- is typed through the model spaces, which are the tangent spaces only up to unfolding
    -- `TangentSpace`.
    rfl
  have hc : Tendsto c (𝓝 (f, x)) (𝓝 (c (f, x))) := by
    have hf₀ : f.toContMDiffMap ((extChartAt I x).symm (extChartAt I x x)) ∈
        (extChartAt J y).source := by
      rw [extChartAt_to_inv, coe_toContMDiffMap]
      exact mem_extChartAt_source y
    have h := TauCeti.tendsto_fderivWithin_extChartAt hn1 (mem_extChartAt_target x) hf₀
    simp only [coe_toContMDiffMap] at h
    refine Tendsto.congr (fun p ↦ ?_) (h.comp (Tendsto.prodMk
      ((continuous_toContMDiffMap.comp continuous_fst).tendsto (f, x)) 
      (?_ : Tendsto (fun p : (M ≃ₘ^n⟮I, J⟯ N) × M ↦ extChartAt I x p.2) _ _)))
    · simp only [Function.comp_apply, coe_toContMDiffMap, c]
    refine tendsto_nhdsWithin_iff.2
      ⟨(continuousAt_extChartAt x).tendsto.comp (continuous_snd.tendsto (f, x)), ?_⟩
    filter_upwards [hsrc] with p hp
    refine (extChartAt I x).map_source ?_
    rwa [extChartAt_source, ← TangentBundle.trivializationAt_baseSet (I := I) x]
  -- Relative to the derivative at `(f, x)`, the derivative starts at the identity, so its
  -- determinant stays positive.
  set T₀ := T (f, x) hx hy
  let K (p : (M ≃ₘ^n⟮I, J⟯ N) × M) : E →L[ℝ] E := (T₀.symm : E' →L[ℝ] E).comp (c p)
  have hK₀ : K (f, x) = ContinuousLinearMap.id ℝ E := by
    ext v
    simp [K, T₀, hcT (f, x) hx hy]
  have hpos : ∀ᶠ p in 𝓝 (f, x), 0 < (K p).det := by
    have hK : Tendsto K (𝓝 (f, x)) (𝓝 (K (f, x))) := continuousAt_const.clm_comp (f := c) hc
    exact ((ContinuousLinearMap.continuous_det.tendsto _).comp hK).eventually
      (lt_mem_nhds (by simp [hK₀, ContinuousLinearMap.det]))
  -- The orientations, read in the trivializations at `x` and `y`, are locally constant.
  have hloc := o.toVectorBundleOrientation.eventually_mapOrientation_eq o.card_eq e hx
  have hloc' := o'.toVectorBundleOrientation.eventually_mapOrientation_eq o'.card_eq e' hy
  simp only [toVectorBundleOrientation_apply] at hloc hloc'
  have h₀ := (isOrientationPreservingAt_iff_map_eq_of_mem o o' f x y
    (f.mfderivToContinuousLinearEquiv hn x) (f.mfderivToContinuousLinearEquiv_coe hn) hx hy).1 h
  filter_upwards [hsrc, htgt, hpos, (continuous_snd.tendsto (f, x)).eventually hloc,
    (hev.tendsto (f, x)).eventually hloc'] with p hp hq hpos hlp hlq
  refine (isOrientationPreservingAt_iff_map_eq_of_mem o o' p.1 x y
    (p.1.mfderivToContinuousLinearEquiv hn p.2) (p.1.mfderivToContinuousLinearEquiv_coe hn)
    hp hq).2 ?_
  rw [hlp hp, hlq hq]
  refine Eq.trans ((_root_.Orientation.map_eq_map_iff_det_pos _ (T p hp hq).toLinearEquiv
    T₀.toLinearEquiv o.card_eq).2 ?_) h₀
  convert hpos using 2
  ext v
  simp [K, hcT p hp hq]

/-- On a compact manifold, the `C^n` diffeomorphisms preserving an orientation `o` at every point,
`n ≠ 0`, form an open subgroup for the weak Whitney topology. -/
theorem isOpen_orientationPreservingSubgroup (hn : n ≠ 0) (o : Orientation I M ι) :
    IsOpen (orientationPreservingSubgroup hn o : Set (TauCeti.Diff I M n)) := by
  refine isOpen_iff_mem_nhds.2 fun f hf ↦ ?_
  filter_upwards [isCompact_univ.eventually_forall_of_forall_eventually
    (P := fun (g : TauCeti.Diff I M n) x ↦ IsOrientationPreservingAt o o g x) fun x _ ↦
    eventually_isOrientationPreservingAt hn
    (mem_orientationPreservingSubgroup_iff.1 hf x)] with g hg
  exact mem_orientationPreservingSubgroup_iff.2 fun x ↦ hg x (mem_univ x)

/-- On a compact manifold, the `C^n` diffeomorphisms preserving an orientation `o` at every point,
`n ≠ 0`, form a closed subgroup for the weak Whitney topology. -/
theorem isClosed_orientationPreservingSubgroup (hn : n ≠ 0) (o : Orientation I M ι) :
    IsClosed (orientationPreservingSubgroup hn o : Set (TauCeti.Diff I M n)) := by
  refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun f hf ↦ ?_)
  simp only [mem_compl_iff, SetLike.mem_coe, mem_orientationPreservingSubgroup_iff,
    not_forall] at hf
  obtain ⟨x, hx⟩ := hf
  -- `f` reverses `o` at `x`, that is, it preserves `o` and `-o` there, and so do its neighbours.
  have hrev : IsOrientationReversingAt o o f x :=
    (isOrientationPreservingAt_or_isOrientationReversingAt o o f x _
      (f.mfderivToContinuousLinearEquiv_coe hn)).resolve_left hx
  have hev := eventually_isOrientationPreservingAt hn
    ((isOrientationPreservingAt_neg_right o o f x).2 hrev)
  filter_upwards [((continuous_id.prodMk continuous_const :
    Continuous fun g : TauCeti.Diff I M n ↦ (g, x)).tendsto f).eventually hev] with g hg hmem
  exact not_isOrientationPreservingAt_and_isOrientationReversingAt o o g x
    ⟨mem_orientationPreservingSubgroup_iff.1 hmem x,
      (isOrientationPreservingAt_neg_right o o g x).1 hg⟩

/-- On a compact manifold, the `C^n` diffeomorphisms preserving an orientation `o` at every point,
`n ≠ 0`, form an open and closed subgroup for the weak Whitney topology. -/
theorem isClopen_orientationPreservingSubgroup (hn : n ≠ 0) (o : Orientation I M ι) :
    IsClopen (orientationPreservingSubgroup hn o : Set (TauCeti.Diff I M n)) :=
  ⟨isClosed_orientationPreservingSubgroup hn o, isOpen_orientationPreservingSubgroup hn o⟩

end Diffeomorph

namespace SymplecticGeometry

/-- `Diff⁺(S²)` is open and closed in the smooth diffeomorphisms of the Riemann sphere, for the
weak Whitney topology. -/
theorem isClopen_diffPlus :
    IsClopen (diffPlus : Set (TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞)) := by
  rw [diffPlus_def]
  exact Diffeomorph.isClopen_orientationPreservingSubgroup _ _

end SymplecticGeometry

end
