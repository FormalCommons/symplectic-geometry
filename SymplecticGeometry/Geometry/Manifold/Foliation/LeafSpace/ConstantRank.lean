/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Distribution.ConstantRank
public import SymplecticGeometry.Geometry.Manifold.Foliation.LeafSpace.Basic
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# The kernel foliation of a map of constant rank: regularity and fibres

Let `f : M → N` be a smooth map of constant rank `r` between boundaryless real manifolds, the
source modelled on a finite-dimensional space `E`. The kernels of its derivative form a foliation
of `M` (`TauCeti.Foliation.ofConstantRank`). This file shows that this foliation is regular in the
sense of `TauCeti.Foliation.IsRegular`: through every point there is a slice, a transversal that
meets each leaf at most once. It also compares the leaves with the fibres of `f`: each leaf in a
fibre is open in that fibre, so a preconnected fibre is a single leaf, and when every fibre is
preconnected `f` induces an injective map on the leaf space.

## Main results

* `TauCeti.Foliation.isRegular_ofConstantRank`: the kernel foliation of a smooth map of constant
  rank is regular.
* `TauCeti.Foliation.isSlice_ofConstantRank`: a smooth map `s` from the model space of the slices
  is a slice of that foliation when `f ∘ s` and its derivatives are injective.
* `TauCeti.Foliation.eventually_sameLeaf_ofConstantRank`: the points of the fibre through `x`
  near `x` lie on the leaf of `x`.
* `TauCeti.Foliation.sameLeaf_ofConstantRank_of_isPreconnected_preimage_singleton`: two points of
  a preconnected fibre lie on one leaf.
* `TauCeti.Foliation.LeafSpace.injective_lift_ofConstantRank`: if every fibre is preconnected,
  the map induced by `f` on the leaf space is injective.

## Implementation notes

In the coordinates `φ`, `ψ` of Tau Ceti's rank theorem
`ContMDiffOn.exists_openPartialHomeomorph_comp_eq_mfderiv_comp` around a point `x`, with
`φ x = 0`, the map reads as a linear map `A`. Take a complement `W` of `ker A` and a linear
isomorphism `L` from the model space of the slices onto `W`. The slice through `x` is
`u ↦ φ.symm (L u)`, on the open set of `u` with `L u` in the target of `φ`. In the coordinate `ψ`,
`f` along the slice is `A ∘ L`, which is injective. Two points on one leaf have the same image
under `f` (`TauCeti.Foliation.SameLeaf.apply_eq_of_ofConstantRank`), so two points of the slice on
one leaf are equal. The derivative of `f` is injective on the tangent image of the slice, so that
image meets the kernel only in `0`, and it is a complement of the kernel by a dimension count.

In the same coordinates, a point `y` of the fibre through `x` with `φ y` in a ball around `φ x`
inside the target of `φ` is joined to `x` by the preimage of the segment from `φ x` to `φ y`.
Since `A (φ x) = A (φ y)`, the map `f` is constant along that curve, so its velocity lies in the
kernel of the derivative of `f` (`TauCeti.Foliation.sameLeaf_ofConstantRank_of_eqOn`), and
Tau Ceti's `TauCeti.Foliation.sameLeaf_of_contMDiffOn_of_tangent` puts its ends on one leaf.
Mathlib's `IsPreconnected.induction₂` then passes from these neighbourhoods to a whole
preconnected fibre.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (the rank theorem) and Chapter 19
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.4
-/

public section

open Set Function Module TopologicalSpace TauCeti TauCeti.Manifold
open scoped Manifold ContDiff Topology

namespace TauCeti.Foliation

variable {E F H G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {f : M → N} {r : ℕ}

section Regular

variable [IsManifold I (∞ + 1) M] [IsManifold J (∞ + 1) N]

/-- A criterion for a slice of the kernel foliation of a map `f` of constant rank `r`: a smooth
map `s` from an open set of `EuclideanSpace ℝ (Fin (dim E - (dim E - r)))` to the source is a slice
of the foliation by the kernels of the derivative of `f` when `f ∘ s` is injective and, at every
point `u`, the composition of the derivatives of `s` at `u` and of `f` at `s u` is injective. -/
theorem isSlice_ofConstantRank (hf : ContMDiff I J (∞ + 1) f)
    (hr : ∀ x, mfderivRank I J f x = r) (hn : (1 : ℕ∞ω) ≤ ∞)
    {U : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E - (finrank ℝ E - r))))} {s : U → M}
    (hs : ContMDiff (𝓡 (finrank ℝ E - (finrank ℝ E - r))) I ∞ s) (hfs : Injective (f ∘ s))
    (hd : ∀ u, Injective (mfderiv I J f (s u) ∘L
      mfderiv (𝓡 (finrank ℝ E - (finrank ℝ E - r))) I s u)) :
    (ofConstantRank hf hr hn).IsSlice s := by
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
theorem isRegular_ofConstantRank (hf : ContMDiff I J (∞ + 1) f)
    (hr : ∀ x, mfderivRank I J f x = r) (hn : (1 : ℕ∞ω) ≤ ∞) :
    (ofConstantRank hf hr hn).IsRegular := by
  refine isRegular_def.2 fun x ↦ ?_
  have h1 : (1 : ℕ∞ω) ≤ ∞ + 1 := le_add_self
  have h0 : (∞ + 1 : ℕ∞ω) ≠ 0 := ne_of_gt (zero_lt_one.trans_le h1)
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
  obtain ⟨W, hW⟩ := (LinearMap.ker (A : E →ₗ[ℝ] F)).exists_isCompl
  have hd : finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E - (finrank ℝ E - r)))) =
      finrank ℝ W := by
    have := Submodule.finrank_add_eq_of_isCompl hW
    rw [finrank_euclideanSpace_fin]
    omega
  let L : EuclideanSpace ℝ (Fin (finrank ℝ E - (finrank ℝ E - r))) →L[ℝ] E :=
    W.subtypeL.comp (ContinuousLinearEquiv.ofFinrankEq hd).toContinuousLinearMap
  have hAL {w} (hw : A (L w) = 0) : w = 0 := by
    have : L w = 0 := (Submodule.disjoint_def.1 hW.disjoint) _ hw (by simp [L])
    simpa [L] using this
  -- The slice: the preimage under `φ` of the image of `L`.
  let U : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E - (finrank ℝ E - r)))) :=
    ⟨L ⁻¹' φ.target, φ.open_target.preimage L.continuous⟩
  let s : U → M := fun u ↦ φ.symm (L u)
  have hfs (u : U) : ψ (f (s u)) = A (L u) := by
    rw [hA _ (φ.map_target u.property), φ.right_inv u.property]
  have hs : ContMDiff (𝓡 (finrank ℝ E - (finrank ℝ E - r))) I
      (∞ + 1) s := fun u ↦
    (hφi.contMDiffAt (φ.open_target.mem_nhds u.property)).comp u
      (L.contMDiff.contMDiffAt.comp u contMDiff_subtypeVal.contMDiffAt)
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
      mfderiv_comp u (hf.mdifferentiableAt h0) hsu, mfderiv_comp_subtype_val_apply,
      (A ∘L L).mfderiv_eq] at h
    simp only [ContinuousLinearMap.comp_apply, hw, map_zero] at h
    exact h.symm
  -- In the coordinate `ψ`, `f ∘ s` is `A ∘ L`, which is injective.
  have hinj : Injective (f ∘ s) := fun u v huv ↦ by
    have h' : A (L (u - v)) = 0 := by
      rw [map_sub, map_sub, ← hfs, ← hfs, ← comp_apply (f := f), ← comp_apply (f := f), huv,
        sub_self]
    exact Subtype.ext (sub_eq_zero.1 (hAL h'))
  exact ⟨U, s, isSlice_ofConstantRank hf hr hn (hs.of_le le_self_add) hinj hkey,
    ⟨0, by simpa [U, L, hφx] using φ.map_source hxφ⟩, by simp [s, L, ← hφx, φ.left_inv hxφ]⟩

end Regular

section Fibres

variable {n : ℕ∞ω} [IsManifold I (n + 1) M] [IsManifold J (n + 1) N]

/-- A curve, `C¹` on `[a, b]`, along which a map `f` of constant rank is constant stays in one
leaf of the kernel foliation of `f`. -/
theorem sameLeaf_ofConstantRank_of_eqOn (hf : ContMDiff I J (n + 1) f)
    (hr : ∀ x, mfderivRank I J f x = r) (hn : 1 ≤ n) {γ : ℝ → M} {a b s t : ℝ} {y : N}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) (hfγ : EqOn (f ∘ γ) (fun _ ↦ y) (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    (ofConstantRank hf hr hn).SameLeaf (γ s) (γ t) := by
  refine sameLeaf_of_contMDiffOn_of_tangent hγ (fun u hu ↦ ?_) hs ht
  rw [ofConstantRank_distribution, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  by_cases hU : UniqueDiffWithinAt ℝ (Icc a b) u
  · have : IsManifold J 1 N := .of_le (n := n + 1) le_add_self
    rw [← curveVelocityWithin_map ((hf.mdifferentiable (one_pos.trans_le le_add_self).ne') _) hU
      ((hγ u hu).mdifferentiableWithinAt one_ne_zero), curveVelocityWithin_apply,
      mfderivWithin_congr hfγ (hfγ hu), mfderivWithin_const, ContinuousLinearMap.comp_zero]
    exact zero_apply _
  · rw [curveVelocityWithin_eq_zero_of_not_uniqueDiffWithinAt hU, map_zero]

/-- **Leaves are open in the fibres.** For a map `f` of constant rank, every point `y` of the
fibre of `f` through `x` that is close enough to `x` lies on the leaf of `x` of the kernel
foliation of `f`. -/
theorem eventually_sameLeaf_ofConstantRank (hf : ContMDiff I J (n + 1) f)
    (hr : ∀ x, mfderivRank I J f x = r) (hn : 1 ≤ n) (x : M) :
    ∀ᶠ y in 𝓝[f ⁻¹' {f x}] x, (ofConstantRank hf hr hn).SameLeaf x y := by
  have h1 : (1 : ℕ∞ω) ≤ n + 1 := le_add_self
  obtain ⟨φ, ψ, hxφ, -, -, -, hφi, -, -, -, hmap, hlin⟩ :=
    hf.contMDiffOn.exists_openPartialHomeomorph_comp_eq_mfderiv_comp isOpen_univ (mem_univ x) h1
      fun y _ ↦ ((hr y).trans (hr x).symm).le
  -- In the coordinates `φ` and `ψ`, the map reads as the linear map `A`.
  let A : E →L[ℝ] F := (tangentSpaceCastModel J (f x) : TangentSpace J (f x) →L[ℝ] F) ∘L
    mfderiv I J f x ∘L ((tangentSpaceCastModel I x).symm : E →L[ℝ] TangentSpace I x)
  have hA (y : M) (hy : y ∈ φ.source) : ψ (f y) = A (φ y) := hlin y hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 φ.open_target (φ x) (φ.map_source hxφ)
  have hV : φ.source ∩ φ ⁻¹' Metric.ball (φ x) ε ∈ 𝓝 x :=
    Filter.inter_mem (φ.open_source.mem_nhds hxφ)
      ((φ.continuousAt hxφ).preimage_mem_nhds (Metric.ball_mem_nhds _ hε))
  filter_upwards [mem_nhdsWithin_of_mem_nhds hV, self_mem_nhdsWithin] with y ⟨hyφ, hyb⟩ hfy
  -- The preimage under `φ` of the segment from `φ x` to `φ y` is a curve in the fibre.
  let ℓ : ℝ → E := fun t ↦ φ x + t • (φ y - φ x)
  have hℓ : MapsTo ℓ (Icc 0 1) φ.target := fun t ht ↦
    hball ((convex_ball _ _).add_smul_sub_mem (Metric.mem_ball_self hε) hyb ht)
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (φ.symm ∘ ℓ) (Icc 0 1) :=
    (hφi.comp (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff.contMDiffOn
      hℓ).of_le h1
  have hfγ : EqOn (f ∘ φ.symm ∘ ℓ) (fun _ ↦ f x) (Icc 0 1) := fun t ht ↦ by
    have hfy' : A (φ y) = A (φ x) := by rw [← hA y hyφ, ← hA x hxφ, mem_preimage.1 hfy]
    refine ψ.injOn (hmap (φ.map_target (hℓ ht))) (hmap hxφ) ?_
    rw [hA _ (φ.map_target (hℓ ht)), φ.right_inv (hℓ ht), hA x hxφ]
    simp [ℓ, hfy']
  simpa [ℓ, φ.left_inv hxφ, φ.left_inv hyφ] using
    sameLeaf_ofConstantRank_of_eqOn hf hr hn hγ hfγ (left_mem_Icc.2 zero_le_one)
      (right_mem_Icc.2 zero_le_one)

/-- In a preconnected fibre of a map `f` of constant rank, any two points lie on one leaf of the
kernel foliation of `f`. -/
theorem sameLeaf_ofConstantRank_of_isPreconnected_preimage_singleton
    (hf : ContMDiff I J (n + 1) f) (hr : ∀ x, mfderivRank I J f x = r) (hn : 1 ≤ n) {b : N}
    (hb : IsPreconnected (f ⁻¹' {b})) {x y : M} (hx : f x = b) (hy : f y = b) :
    (ofConstantRank hf hr hn).SameLeaf x y :=
  hb.induction₂ (ofConstantRank hf hr hn).SameLeaf (fun z hz ↦ by
      rw [← mem_singleton_iff.1 (mem_preimage.1 hz)]
      exact eventually_sameLeaf_ofConstantRank hf hr hn z)
    (fun _ _ _ _ _ _ ↦ SameLeaf.trans) (fun _ _ _ _ ↦ SameLeaf.symm) hx hy

/-- If every fibre of a map `f` of constant rank is preconnected, the map induced by `f` on the
leaf space of its kernel foliation is injective. -/
theorem LeafSpace.injective_lift_ofConstantRank (hf : ContMDiff I J (n + 1) f)
    (hr : ∀ x, mfderivRank I J f x = r) (hn : 1 ≤ n) (h : ∀ b, IsPreconnected (f ⁻¹' {b})) :
    Injective (LeafSpace.lift f fun _ _ ↦ SameLeaf.apply_eq_of_ofConstantRank (hf := hf)
      (hr := hr) (hn := hn)) := by
  intro p q hpq
  induction p using LeafSpace.ind with | h x => ?_
  induction q using LeafSpace.ind with | h y => ?_
  rw [LeafSpace.lift_leafSpaceMk, LeafSpace.lift_leafSpaceMk] at hpq
  exact leafSpaceMk_eq_leafSpaceMk_iff.2
    (sameLeaf_ofConstantRank_of_isPreconnected_preimage_singleton hf hr hn (h (f y)) hpq rfl)

end Fibres

end TauCeti.Foliation

end
