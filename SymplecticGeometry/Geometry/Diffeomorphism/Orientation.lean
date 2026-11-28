/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Congr
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import SymplecticGeometry.Geometry.Manifold.Orientation.Diffeomorph
import Mathlib.Topology.Algebra.OpenSubgroup
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Chart
import SymplecticGeometry.Geometry.Manifold.Orientation.Preserving
import SymplecticGeometry.Geometry.Manifold.Orientation.Reindex
import TauCeti.Geometry.Diffeomorphism.Composition
import TauCeti.Geometry.Diffeomorphism.Evaluation
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Differential

/-!
# The orientation-preserving subgroup of a diffeomorphism group

Tau Ceti's `Diffeomorph.orientationPreservingSubgroup hn o` is the subgroup of `C^n`
self-diffeomorphisms of a manifold `M` that preserve an orientation `o` at every point. This file
shows how it depends on `o`, how it behaves under conjugation, and that it is open and closed for
the weak Whitney topology when `M` is compact.

* `Diffeomorph.orientationPreservingSubgroup_neg`: a diffeomorphism preserves `o` exactly when it
  preserves `-o`, so the subgroup is the same for both.
* `Diffeomorph.orientationPreservingSubgroup_reindex`: reindexing `o` does not change the subgroup.
* `Diffeomorph.map_orientationPreservingSubgroup_diffCongr`: conjugation by a diffeomorphism
  `e : M → N`, Tau Ceti's `Diffeomorph.diffCongr e`, maps the subgroup for `o` onto the subgroup
  for the orientation `o.map e hn hι` carried to `N` along `e`.
* `TauCeti.range_orthogonalToDiffSphere_specialOrthogonalGroup_le`: the rotations `SO(n + 1)`,
  restricted to the unit sphere `Sⁿ` by `TauCeti.orthogonalToDiffSphere n m`, preserve the
  outward-normal orientation `o.sphereOrientation` of every orientation `o` of `ℝⁿ⁺¹`, by Tau
  Ceti's `Orientation.isOrientationPreservingAt_unitSphereEquiv`.

## Openness and closedness for the weak Whitney topology

On a compact manifold, with Tau Ceti's weak Whitney topology on diffeomorphisms:

* `Diffeomorph.eventually_isOrientationPreservingAt`: if a diffeomorphism preserves orientations at
  a point, then so does every nearby diffeomorphism at every nearby point. The derivative, read in
  the tangent trivializations at the base point and its image, is the chart differential
  (`ContinuousAt.fderivWithin_extChartAt_comp_extChartAt_symm_eq_trivializationAt`). That varies
  continuously with the pair, by Tau Ceti's `TauCeti.tendsto_fderivWithin_extChartAt`, so its
  determinant relative to the derivative at the base pair stays positive. The orientations, read in
  those trivializations, are locally constant. The argument adapts Tau Ceti's
  `TauCeti.Manifold.Orientation.isLocallyConstant_isOrientationPreservingAt`, which treats a
  jointly `C¹` family with a fixed source point, to a weak Whitney neighbourhood and a moving point.
* `Diffeomorph.isOpen_orientationPreservingSubgroup`: the subgroup is open, by the tube lemma
  `IsCompact.eventually_forall_of_forall_eventually`;
* `Diffeomorph.isClosed_orientationPreservingSubgroup`: it is closed, as every open subgroup of a
  group with separately continuous multiplication is (`Subgroup.isClosed_of_isOpen`);
* `Diffeomorph.isClopen_orientationPreservingSubgroup`: both together.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Graduate Texts in Mathematics 33,
  Springer, 1976, Chapter 2, §1 (the weak topology).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15.
-/

public section

open Module TauCeti.Manifold

open scoped Manifold ContDiff

namespace Diffeomorph

variable {E E' H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H]
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [TopologicalSpace N]
  [ChartedSpace H' N] [IsManifold I' 1 N] {ι : Type*} [Fintype ι] {n : ℕ∞ω}

/-- A diffeomorphism preserves an orientation at every point exactly when it preserves the
opposite orientation at every point. -/
@[simp]
theorem orientationPreservingSubgroup_neg (hn : n ≠ 0) (o : Orientation I M ι) :
    orientationPreservingSubgroup hn (-o) = orientationPreservingSubgroup hn o := by
  ext f
  simp only [mem_orientationPreservingSubgroup_iff, Orientation.isOrientationPreservingAt_neg_left,
    Orientation.isOrientationReversingAt_neg_right]

/-- Reindexing an orientation does not change the diffeomorphisms that preserve it. -/
@[simp]
theorem orientationPreservingSubgroup_reindex (hn : n ≠ 0) (o : Orientation I M ι)
    {ι' : Type*} [Fintype ι'] (σ : ι ≃ ι') :
    orientationPreservingSubgroup hn (o.reindex σ) = orientationPreservingSubgroup hn o := by
  ext f
  simp [mem_orientationPreservingSubgroup_iff]

/-- Conjugation by a diffeomorphism `e : M → N`, `φ ↦ e ∘ φ ∘ e⁻¹`, maps the diffeomorphisms of
`M` preserving an orientation `o` onto the diffeomorphisms of `N` preserving the orientation
carried from `o` along `e`. -/
theorem map_orientationPreservingSubgroup_diffCongr (hn : n ≠ 0) (o : Orientation I M ι)
    (e : M ≃ₘ^n⟮I, I'⟯ N) (hι : Fintype.card ι = finrank ℝ E') :
    (orientationPreservingSubgroup hn o).map (diffCongr e).toMonoidHom =
      orientationPreservingSubgroup hn (o.map e hn hι) := by
  ext ψ
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, mem_orientationPreservingSubgroup_iff]
  constructor
  · rintro ⟨φ, hφ, rfl⟩ y
    have hcoe : ⇑(diffCongr e φ) = e ∘ φ ∘ e.symm := funext (diffCongr_apply_apply e φ)
    rw [hcoe]
    exact (Orientation.isOrientationPreservingAt_map o e hn hι _).comp
      ((hφ _).comp (Orientation.isOrientationPreservingAt_map_symm o e hn hι y))
  · intro hψ
    refine ⟨(diffCongr e).symm ψ, fun x ↦ ?_, MulEquiv.apply_symm_apply _ ψ⟩
    have hcoe : ⇑((diffCongr e).symm ψ) = e.symm ∘ ψ ∘ e := by
      rw [diffCongr_symm]
      exact funext (diffCongr_apply_apply e.symm ψ)
    rw [hcoe]
    exact (Orientation.isOrientationPreservingAt_map_symm o e hn hι _).comp
      ((hψ _).comp (Orientation.isOrientationPreservingAt_map o e hn hι x))


section WeakWhitney

open Filter Set Topology

open scoped TauCeti.DiffeomorphWeakWhitney TauCeti.ManifoldWeakWhitney

variable [CompactSpace M] [IsManifold I n M] [IsManifold I' n N]

open TauCeti.Manifold.Orientation in
/-- **Orientation preservation is open in the diffeomorphism and the point.** If a `C^n`
diffeomorphism `f` from a compact manifold, `n ≠ 0`, preserves the orientations `o` and `o'` at
`x`, then every diffeomorphism near `f` in the weak Whitney topology preserves them at every
point near `x`. -/
theorem eventually_isOrientationPreservingAt (hn : n ≠ 0) {o : Orientation I M ι}
    {o' : Orientation I' N ι} {f : M ≃ₘ^n⟮I, I'⟯ N} {x : M}
    (h : IsOrientationPreservingAt o o' f x) :
    ∀ᶠ p : (M ≃ₘ^n⟮I, I'⟯ N) × M in 𝓝 (f, x), IsOrientationPreservingAt o o' p.1 p.2 := by
  have hn1 : 1 ≤ n := ENat.one_le_iff_ne_zero_withTop.mpr hn
  set y := f x
  set e := trivializationAt E (TangentSpace I) x
  set e' := trivializationAt E' (TangentSpace I') y
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hy : y ∈ e'.baseSet := FiberBundle.mem_baseSet_trivializationAt' y
  have hev : Continuous fun p : (M ≃ₘ^n⟮I, I'⟯ N) × M ↦ p.1 p.2 := continuous_eval
  have hsrc : ∀ᶠ p : (M ≃ₘ^n⟮I, I'⟯ N) × M in 𝓝 (f, x), p.2 ∈ e.baseSet :=
    continuous_snd.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hx)
  have htgt : ∀ᶠ p : (M ≃ₘ^n⟮I, I'⟯ N) × M in 𝓝 (f, x), p.1 p.2 ∈ e'.baseSet :=
    hev.continuousAt.preimage_mem_nhds (e'.open_baseSet.mem_nhds hy)
  -- The derivative of `p.1` at `p.2`, read in the trivializations at `x` and `y`.
  let T (p : (M ≃ₘ^n⟮I, I'⟯ N) × M) (hp : p.2 ∈ e.baseSet) (hq : p.1 p.2 ∈ e'.baseSet) :
      E ≃L[ℝ] E' :=
    ((e.continuousLinearEquivAt ℝ p.2 hp).symm.trans
      (p.1.mfderivToContinuousLinearEquiv hn p.2)).trans
        (e'.continuousLinearEquivAt ℝ (p.1 p.2) hq)
  -- The same derivative as a chart differential, which varies continuously with `p`.
  let c (p : (M ≃ₘ^n⟮I, I'⟯ N) × M) : E →L[ℝ] E' :=
    fderivWithin ℝ (extChartAt I' y ∘ p.1 ∘ (extChartAt I x).symm) (extChartAt I x).target
      (extChartAt I x p.2)
  have hcT (p : (M ≃ₘ^n⟮I, I'⟯ N) × M) (hp : p.2 ∈ e.baseSet) (hq : p.1 p.2 ∈ e'.baseSet) :
      c p = (T p hp hq : E →L[ℝ] E') := by
    have h₃ := DFunLike.congr_fun (p.1.mfderivToContinuousLinearEquiv_coe hn (x := p.2))
    simp only [ContinuousLinearEquiv.coe_coe] at h₃
    ext v
    simp only [c, T,
      p.1.continuous.continuousAt.fderivWithin_extChartAt_comp_extChartAt_symm_eq_trivializationAt
        hp hq, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.trans_apply, h₃]
    rw [← ContinuousLinearEquiv.coe_coe (e'.continuousLinearEquivAt ℝ _ hq),
      e'.coe_continuousLinearEquivAt_eq' hq,
      ← ContinuousLinearEquiv.coe_coe (e.continuousLinearEquivAt ℝ _ hp).symm,
      e.symm_continuousLinearEquivAt_eq' hp]
  have hc : Tendsto c (𝓝 (f, x)) (𝓝 (c (f, x))) := by
    have hf₀ : f.toContMDiffMap ((extChartAt I x).symm (extChartAt I x x)) ∈
        (extChartAt I' y).source := by
      rw [extChartAt_to_inv, coe_toContMDiffMap]
      exact mem_extChartAt_source y
    have h := TauCeti.tendsto_fderivWithin_extChartAt hn1 (mem_extChartAt_target x) hf₀
    simp only [coe_toContMDiffMap] at h
    refine Tendsto.congr (fun p ↦ ?_) (h.comp (Tendsto.prodMk
      ((continuous_toContMDiffMap.comp continuous_fst).tendsto (f, x))
      (?_ : Tendsto (fun p : (M ≃ₘ^n⟮I, I'⟯ N) × M ↦ extChartAt I x p.2) _ _)))
    · simp only [Function.comp_apply, coe_toContMDiffMap, c]
    refine tendsto_nhdsWithin_iff.2
      ⟨(continuousAt_extChartAt x).tendsto.comp (continuous_snd.tendsto (f, x)), ?_⟩
    filter_upwards [hsrc] with p hp
    refine (extChartAt I x).map_source ?_
    rwa [extChartAt_source, ← TangentBundle.trivializationAt_baseSet (I := I) x]
  -- Relative to the derivative at `(f, x)`, the derivative starts at the identity, so its
  -- determinant stays positive.
  set T₀ := T (f, x) hx hy
  let K (p : (M ≃ₘ^n⟮I, I'⟯ N) × M) : E →L[ℝ] E := (T₀.symm : E' →L[ℝ] E).comp (c p)
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
    (P := fun (g : TauCeti.Diff I M n) x ↦ Orientation.IsOrientationPreservingAt o o g x)
    fun x _ ↦ eventually_isOrientationPreservingAt hn
    (mem_orientationPreservingSubgroup_iff.1 hf x)] with g hg
  exact mem_orientationPreservingSubgroup_iff.2 fun x ↦ hg x (mem_univ x)

/-- On a compact manifold, the `C^n` diffeomorphisms preserving an orientation `o` at every point,
`n ≠ 0`, form a closed subgroup for the weak Whitney topology. -/
theorem isClosed_orientationPreservingSubgroup (hn : n ≠ 0) (o : Orientation I M ι) :
    IsClosed (orientationPreservingSubgroup hn o : Set (TauCeti.Diff I M n)) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_orientationPreservingSubgroup hn o)

/-- On a compact manifold, the `C^n` diffeomorphisms preserving an orientation `o` at every point,
`n ≠ 0`, form an open and closed subgroup for the weak Whitney topology. -/
theorem isClopen_orientationPreservingSubgroup (hn : n ≠ 0) (o : Orientation I M ι) :
    IsClopen (orientationPreservingSubgroup hn o : Set (TauCeti.Diff I M n)) :=
  ⟨isClosed_orientationPreservingSubgroup hn o, isOpen_orientationPreservingSubgroup hn o⟩

end WeakWhitney
end Diffeomorph

namespace TauCeti

open Metric Matrix

/-- The rotations `SO(n + 1)` of `ℝⁿ⁺¹` restrict to diffeomorphisms of the unit sphere `Sⁿ` that
preserve the outward-normal orientation `o.sphereOrientation` at every point, for every
orientation `o` of `ℝⁿ⁺¹`. -/
theorem range_orthogonalToDiffSphere_specialOrthogonalGroup_le {n : ℕ}
    [Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1)] {m : ℕ∞ω} (hm : m ≠ 0)
    (o : _root_.Orientation ℝ (EuclideanSpace ℝ (Fin (n + 1))) (Fin (n + 1))) :
    ((orthogonalToDiffSphere n m).comp
      (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)).range ≤
      Diffeomorph.orientationPreservingSubgroup hm o.sphereOrientation := by
  rintro _ ⟨A, rfl⟩
  rw [Diffeomorph.mem_orientationPreservingSubgroup_iff]
  intro u
  rw [MonoidHom.comp_apply, orthogonalToDiffSphere_apply,
    LinearIsometryEquiv.unitSphereDiffHom_apply, LinearIsometryEquiv.coe_unitSphereDiffeomorph]
  refine o.isOrientationPreservingAt_unitSphereEquiv ?_ u
  set e := UnitaryGroup.toLinearIsometryEquiv
    (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup A)
  have he : (e.toLinearEquiv : _ →ₗ[ℝ] _) = e.toLinearIsometry.toLinearMap :=
    LinearMap.ext fun _ ↦ by simp
  rw [he, UnitaryGroup.det_toLinearIsometryEquiv, Submonoid.coe_inclusion,
    (mem_specialOrthogonalGroup_iff.1 A.property).2]
  exact one_pos

end TauCeti

end
