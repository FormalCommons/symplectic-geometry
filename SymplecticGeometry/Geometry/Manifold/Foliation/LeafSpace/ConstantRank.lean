/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Distribution.ConstantRank
public import SymplecticGeometry.Geometry.Manifold.Foliation.LeafSpace.Smooth
public import TauCeti.Geometry.Manifold.Submersion.Descent
import Mathlib.Geometry.Manifold.Instances.Real
import SymplecticGeometry.Topology.Algebra.Module.FiniteDimension
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.ConstantRank.Basic

/-!
# The kernel foliation of a map of constant rank is regular

Let `f : M → N` be a smooth map of constant rank `r` between boundaryless real manifolds, the
source modelled on a finite-dimensional space `E`. The kernels of its derivative form a foliation
of `M` (`TauCeti.Foliation.ofConstantRank`). This file shows that this foliation is regular in the
sense of `TauCeti.Foliation.IsRegular`: through every point there is a slice, a transversal that
meets each leaf at most once. With the charts of `TauCeti.Foliation.leafSpaceChartedSpace`, the
map that `f` induces on the leaf space is then an immersion.

## Main results

* `TauCeti.Foliation.isRegular_ofConstantRank`: the kernel foliation of a smooth map of constant
  rank is regular.
* `TauCeti.Foliation.isSlice_ofConstantRank`: a smooth map `s` from the model space of the slices
  is a slice of that foliation when `f ∘ s` and its derivatives are injective.
* `TauCeti.Foliation.ker_mfderiv_leafSpaceMk_ofConstantRank`: the projection onto the leaf space
  of that foliation has the same kernels as the derivative of `f`.
* `TauCeti.Foliation.LeafSpace.isImmersion_lift_ofConstantRank`: the map induced by `f` on that
  leaf space is an immersion.
* `TauCeti.Foliation.LeafSpace.injective_lift_ofConstantRank`: if every fibre is preconnected,
  the map induced by `f` on the leaf space is injective.
* `TauCeti.Foliation.LeafSpace.t2Space_ofConstantRank`: if moreover `N` is Hausdorff, so is that
  leaf space.

## Implementation notes

In the coordinates `φ`, `ψ` of Tau Ceti's rank theorem
`ContMDiffOn.exists_openPartialHomeomorph_comp_eq_mfderiv_comp` around a point `x`, with
`φ x = 0`, the map reads as a linear map `A`. Take an injective linear map `L` from
the model space of the slices whose range is a complement of `ker A`
(`Submodule.exists_continuousLinearMap_injective_isCompl_range`). The slice through `x` is
`u ↦ φ.symm (L u)`, on the open set of `u` with `L u` in the target of `φ`. In the coordinate `ψ`,
`f` along the slice is `A ∘ L`, which is injective. Two points on one leaf have the same image
under `f` (`TauCeti.Foliation.SameLeaf.apply_eq_of_ofConstantRank`), so two points of the slice on
one leaf are equal. The derivative of `f` is injective on the tangent image of the slice, so that
image meets the kernel only in `0`, and it is a complement of the kernel by a dimension count.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (the rank theorem) and Chapter 19
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.4
-/

public section

open Set Function Module TopologicalSpace TauCeti TauCeti.Manifold
open scoped Manifold ContDiff

namespace TauCeti.Foliation

variable {E F H G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {f : M → N} {r : ℕ}

section Regular

variable [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- A criterion for a slice of the kernel foliation of a map `f` of constant rank `r`: a smooth
map `s` from an open set of `EuclideanSpace ℝ (Fin (dim E - (dim E - r)))` to the source is a slice
of the foliation by the kernels of the derivative of `f` when `f ∘ s` is injective and, at every
point `u`, the composition of the derivatives of `s` at `u` and of `f` at `s u` is injective. -/
theorem isSlice_ofConstantRank (hf : ContMDiff I J ∞ f) (hr : ∀ x, mfderivRank I J f x = r)
    {U : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E - (finrank ℝ E - r))))} {s : U → M}
    (hs : ContMDiff (𝓡 (finrank ℝ E - (finrank ℝ E - r))) I ∞ s) (hfs : Injective (f ∘ s))
    (hd : ∀ u, Injective (mfderiv I J f (s u) ∘L
      mfderiv (𝓡 (finrank ℝ E - (finrank ℝ E - r))) I s u)) :
    (ofConstantRank (n := ∞) (hf.of_le ENat.coe_top_add_one.le) hr ENat.LEInfty.out).IsSlice
      s := by
  refine ⟨hs, fun u ↦ ?_, fun u v huv ↦ hfs (huv.apply_eq_of_ofConstantRank)⟩
  rw [ofConstantRank_distribution]
  have hinj : Injective (mfderiv (𝓡 (finrank ℝ E - (finrank ℝ E - r))) I s u) := by
    have h := hd u
    rw [ContinuousLinearMap.coe_comp] at h
    exact h.of_comp
  have hr' := finrank_ker_mfderiv_add_mfderivRank (I := I) (J := J) (f := f) (x := s u)
  rw [hr] at hr'
  have hrange := LinearMap.finrank_range_of_inj (f := (mfderiv
    (𝓡 (finrank ℝ E - (finrank ℝ E - r))) I s u).toLinearMap) hinj
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).2 (Submodule.disjoint_def.2 ?_)
  · rw [hrange]
    simp only [finrank_tangentSpace, finrank_euclideanSpace_fin]
    omega
  · rintro _ ⟨w, rfl⟩ hw
    have h0 : (mfderiv I J f (s u) ∘L
        mfderiv (𝓡 (finrank ℝ E - (finrank ℝ E - r))) I s u) w = 0 := by
      rw [ContinuousLinearMap.comp_apply]
      exact hw
    rw [hd u (h0.trans (map_zero _).symm)]
    exact map_zero _

/-- **The kernel foliation of a map of constant rank is regular.** For a smooth map `f` of
constant rank `r` between boundaryless real manifolds, the source modelled on a
finite-dimensional space, every point lies on a slice of the foliation of the source by the
kernels of the derivative of `f`. -/
theorem isRegular_ofConstantRank (hf : ContMDiff I J ∞ f) (hr : ∀ x, mfderivRank I J f x = r) :
    (ofConstantRank (n := ∞) (hf.of_le ENat.coe_top_add_one.le) hr
      ENat.LEInfty.out).IsRegular := by
  refine isRegular_def.2 fun x ↦ ?_
  have h1 : (1 : ℕ∞ω) ≤ ∞ := ENat.LEInfty.out
  have h0 : (∞ : ℕ∞ω) ≠ 0 := ne_of_gt (zero_lt_one.trans_le h1)
  obtain ⟨φ, ψ, hxφ, -, hφx, -, hφi, -, hψ, -, hmap, hlin⟩ :=
    hf.contMDiffOn.exists_openPartialHomeomorph_comp_eq_mfderiv_comp isOpen_univ (mem_univ x) h1
      fun y _ ↦ ((hr y).trans (hr x).symm).le
  -- In the coordinates `φ` and `ψ`, the map reads as the linear map `A`.
  let A : E →L[ℝ] F := (tangentSpaceCastModel J (f x) : TangentSpace J (f x) →L[ℝ] F) ∘L
    mfderiv I J f x ∘L ((tangentSpaceCastModel I x).symm : E →L[ℝ] TangentSpace I x)
  have hA (y : M) (hy : y ∈ φ.source) : ψ (f y) = A (φ y) := hlin y hy
  have hkr := finrank_ker_mfderiv_add_mfderivRank (I := I) (J := J) (f := f) (x := x)
  rw [hr x] at hkr
  have hK : finrank ℝ (LinearMap.ker (A : E →ₗ[ℝ] F)) = finrank ℝ E - r := by
    have hcomp : LinearMap.ker (A : E →ₗ[ℝ] F) = (mfderiv I J f x).ker.map
        ((tangentSpaceCastModel I x).toLinearEquiv : TangentSpace I x →ₗ[ℝ] E) := by
      ext v
      simp [A, Submodule.mem_map_equiv]
    rw [hcomp, LinearEquiv.finrank_map_eq]
    omega
  -- A complement of `ker A`, parametrized linearly by the model space of the slices.
  obtain ⟨L, hL, hW⟩ :=
    (LinearMap.ker (A : E →ₗ[ℝ] F)).exists_continuousLinearMap_injective_isCompl_range
      (F := EuclideanSpace ℝ (Fin (finrank ℝ E - (finrank ℝ E - r))))
      (by rw [finrank_euclideanSpace_fin, hK]; omega)
  have hAL {w} (hw : A (L w) = 0) : w = 0 :=
    hL (((Submodule.disjoint_def.1 hW.disjoint) _ hw (LinearMap.mem_range_self _ _)).trans
      (map_zero L).symm)
  -- The slice: the preimage under `φ` of the image of `L`.
  let U : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E - (finrank ℝ E - r)))) :=
    ⟨L ⁻¹' φ.target, φ.open_target.preimage L.continuous⟩
  let s : U → M := fun u ↦ φ.symm (L u)
  have hfs (u : U) : ψ (f (s u)) = A (L u) := by
    rw [hA _ (φ.map_target u.property), φ.right_inv u.property]
  have hs : ContMDiff (𝓡 (finrank ℝ E - (finrank ℝ E - r))) I ∞ s :=
    hφi.comp_contMDiff (L.contMDiff.comp contMDiff_subtypeVal) fun u ↦ u.property
  -- In the coordinate `ψ`, the derivative of `f ∘ s` is `A ∘ L`, which is injective.
  have hkey (u : U) : Injective (mfderiv I J f (s u) ∘L
      mfderiv (𝓡 (finrank ℝ E - (finrank ℝ E - r))) I s u) := by
    refine (injective_iff_map_eq_zero _).2 fun w hw ↦ hAL ?_
    rw [ContinuousLinearMap.comp_apply] at hw
    have hψu : MDifferentiableAt J 𝓘(ℝ, F) ψ (f (s u)) :=
      (hψ.contMDiffAt (ψ.open_source.mem_nhds (hmap (φ.map_target u.property)))).mdifferentiableAt
        h0
    have hsu := (hs u).mdifferentiableAt h0
    have hcomp : ψ ∘ f ∘ s = (A ∘L L) ∘ Subtype.val := funext hfs
    have h : mfderiv (𝓡 (finrank ℝ E - (finrank ℝ E - r))) 𝓘(ℝ, F)
        (ψ ∘ f ∘ s) u w = mfderiv (𝓡 (finrank ℝ E - (finrank ℝ E - r)))
          𝓘(ℝ, F) ((A ∘L L) ∘ Subtype.val) u w := by
      rw [hcomp]
    rw [mfderiv_comp u hψu ((hf.mdifferentiableAt h0).comp u hsu),
      mfderiv_comp u (hf.mdifferentiableAt h0) hsu, mfderiv_modelSpace_comp_subtypeVal_apply,
      (A ∘L L).fderiv] at h
    simp only [ContinuousLinearMap.comp_apply, hw, map_zero] at h
    exact h.symm
  -- In the coordinate `ψ`, `f ∘ s` is `A ∘ L`, which is injective.
  have hinj : Injective (f ∘ s) := fun u v huv ↦ by
    have h' : A (L (u - v)) = 0 := by
      rw [map_sub, map_sub, ← hfs, ← hfs, ← comp_apply (f := f), ← comp_apply (f := f), huv,
        sub_self]
    exact Subtype.ext (sub_eq_zero.1 (hAL h'))
  exact ⟨U, s, isSlice_ofConstantRank hf hr hs hinj hkey,
    ⟨0, by simpa [U, hφx] using φ.map_source hxφ⟩, by simp [s, ← hφx, φ.left_inv hxφ]⟩

/-- The kernel of the differential at `x` of the projection onto the leaf space of the kernel
foliation of a smooth map `f` of constant rank is the kernel of the differential of `f` at `x`. -/
theorem ker_mfderiv_leafSpaceMk_ofConstantRank (hf : ContMDiff I J ∞ f)
    (hr : ∀ x, mfderivRank I J f x = r) (x : M) :
    letI := leafSpaceChartedSpace (isRegular_ofConstantRank hf hr)
    (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - (finrank ℝ E - r))))
      (ofConstantRank (n := ∞) (hf.of_le ENat.coe_top_add_one.le) hr
        ENat.LEInfty.out).leafSpaceMk x).ker = (mfderiv I J f x).ker :=
  (ker_mfderiv_leafSpaceMk (isRegular_ofConstantRank hf hr) x).trans
    (ofConstantRank_distribution _ hr _ x)

/-- **The map induced on the leaf space of the kernel foliation is an immersion.** For a smooth
map `f` of constant rank `r` between boundaryless real manifolds modelled on finite-dimensional
spaces, the map that `f` induces on the leaf space of the foliation of the source by the kernels
of the derivative of `f` is an immersion. -/
theorem LeafSpace.isImmersion_lift_ofConstantRank [FiniteDimensional ℝ F]
    (hf : ContMDiff I J ∞ f) (hr : ∀ x, mfderivRank I J f x = r) :
    letI := leafSpaceChartedSpace (isRegular_ofConstantRank hf hr)
    Manifold.IsImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - (finrank ℝ E - r)))) J ∞
      (LeafSpace.lift f fun _ _ ↦ SameLeaf.apply_eq_of_ofConstantRank
        (hf := hf.of_le ENat.coe_top_add_one.le) (hr := hr) (hn := ENat.LEInfty.out)) := by
  have hR := isRegular_ofConstantRank hf hr
  let := leafSpaceChartedSpace hR
  have := isManifold_leafSpace hR
  refine ((isSubmersion_leafSpaceMk hR).isImmersion_iff_ker_mfderiv_comp leafSpaceMk_surjective
    (by simp)).2 ⟨?_, fun x ↦ ?_⟩ <;> rw [LeafSpace.lift_comp_leafSpaceMk]
  · exact hf
  · exact (ker_mfderiv_leafSpaceMk_ofConstantRank hf hr x).symm

end Regular

section Fibres

variable {n : ℕ∞ω} [IsManifold I (n + 1) M] [IsManifold J (n + 1) N]

/-- If every fibre of a map `f` of constant rank is preconnected, the map induced by `f` on the
leaf space of its kernel foliation is injective. -/
theorem LeafSpace.injective_lift_ofConstantRank (hf : ContMDiff I J (n + 1) f)
    (hr : ∀ x, mfderivRank I J f x = r) (hn : 1 ≤ n) (h : ∀ b, IsPreconnected (f ⁻¹' {b})) :
    Injective (LeafSpace.lift f fun _ _ ↦ SameLeaf.apply_eq_of_ofConstantRank (hf := hf)
      (hr := hr) (hn := hn)) :=
  LeafSpace.injective_lift_iff.2 fun _ y hxy ↦
    sameLeaf_ofConstantRank_of_isPreconnected_preimage_singleton hf hr hn (h (f y)) hxy rfl

/-- If every fibre of a map `f` of constant rank into a Hausdorff space is preconnected, the leaf
space of its kernel foliation is Hausdorff. -/
theorem LeafSpace.t2Space_ofConstantRank [T2Space N] (hf : ContMDiff I J (n + 1) f)
    (hr : ∀ x, mfderivRank I J f x = r) (hn : 1 ≤ n) (h : ∀ b, IsPreconnected (f ⁻¹' {b})) :
    T2Space (ofConstantRank hf hr hn).LeafSpace :=
  T2Space.of_injective_continuous (LeafSpace.injective_lift_ofConstantRank hf hr hn h)
    (LeafSpace.continuous_lift hf.continuous)

end Fibres

end TauCeti.Foliation

end
