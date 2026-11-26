/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.ConstantRank.Basic
public import TauCeti.Geometry.Manifold.Distribution.Kernel
public import TauCeti.Geometry.Manifold.Foliation.Leaf
public import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Distribution.Diffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.RegularValue
import SymplecticGeometry.Algebra.Order.Monoid.NatCast
import SymplecticGeometry.Geometry.Manifold.ContMDiff.LineMap
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Curve
import SymplecticGeometry.Geometry.Manifold.Foliation.Constancy
import SymplecticGeometry.Geometry.Manifold.RegularValue.Submersion

/-!
# The kernel foliation of a map of constant rank

Let `f : M → N` be a smooth map of constant rank `r` between boundaryless manifolds, the source
modelled on a finite-dimensional space `E`. The kernels of its derivative form a smooth
distribution of rank `dim E - r`, and, being involutive, a foliation of `M`. Over `ℝ`, where
Tau Ceti defines the leaves of a foliation, each leaf lies in a fibre of `f`.

## Main results

* `ContMDiff.isContMDiffDistribution_ker_mfderiv`: for a `C^n` map of constant rank `r`, the
  kernels `ker (mfderiv f x)` form a `C^m` distribution of rank `dim E - r` when `m + 1 ≤ n`.
* `TauCeti.Foliation.ofConstantRank`: the foliation of `M` by these kernels, with
  `TauCeti.Foliation.ofConstantRank_distribution`.
* `TauCeti.Foliation.SameLeaf.apply_eq_of_ofConstantRank`: a real map of constant rank is
  constant on each leaf of its kernel foliation.
* `TauCeti.Foliation.eventually_sameLeaf_ofConstantRank`: conversely, the points of the fibre
  through `x` near `x` lie on the leaf of `x`.
* `TauCeti.Foliation.sameLeaf_ofConstantRank_of_isPreconnected_preimage_singleton`: two points of
  a preconnected fibre lie on one leaf.
* `Manifold.IsSubmersion.mfderivRank_eq`: a submersion has constant rank `dim F`, so the fibres
  of a submersion give an example of the construction.

## Implementation notes

In the partial diffeomorphisms `Φ`, `Ψ` that the rank theorem
`ContMDiffOn.exists_partialDiffeomorph_comp_eq_mfderivModel_comp` gives around a point `x`, the map
reads as the linear map `A = mfderivModel I J f x`. On the source of `Φ`, the kernel of
`mfderiv f y` is the preimage under `mfderiv Φ y` of the fixed subspace `ker A` (by Tau Ceti's
`IsLocalDiffeomorphAt.ker_mfderiv_comp` for `Ψ`), so pulling back through `Φ`, by
`TauCeti.IsDistributionFrameOn.comap_mfderivWithin`, a constant frame of `ker A` from
`TauCeti.isContMDiffDistribution_const` gives a local frame. This is the argument
of Tau Ceti's `Manifold.IsSubmersionAtOfComplement.isDistributionFrameOn_ker_mfderiv`, whose proof
the proof of `ContMDiff.isContMDiffDistribution_ker_mfderiv` adapts, with the rank theorem's
coordinates in place of the normal form of a submersion. Involutivity is Tau Ceti's
`ContMDiff.isInvolutiveDistribution_ker_mfderiv`.

For the converse, Tau Ceti's `ContMDiffOn.exists_openPartialHomeomorph_apply_eq_iff_mem_ker`
gives a chart `φ` with `φ x = 0` that maps the points of the fibre through `x` in its source into
the kernel of the derivative at `x`, and only those. For `y` in that fibre with `φ y` in a ball
inside the target of `φ`, the preimage under `φ` of the segment `t ↦ t • φ y` is a curve along
which `f` is constant, so its velocity lies in the kernel
(`TauCeti.Foliation.sameLeaf_ofConstantRank_of_eqOn`), and Tau Ceti's
`TauCeti.Foliation.sameLeaf_of_contMDiffOn_of_tangent` puts `x` and `y` on one leaf. Mathlib's
`IsPreconnected.induction₂` passes from these neighbourhoods to a whole preconnected fibre.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (the rank theorem) and Chapter 19 (distributions and foliations).
-/

public section

noncomputable section

open Set Function Module TauCeti SymplecticGeometry
open scoped Manifold ContDiff Topology

namespace Manifold.IsSubmersion

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [FiniteDimensional 𝕜 F] [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N}

/-- A submersion has constant rank: at every point, its rank is the dimension of the model space
`F` of the target. -/
theorem mfderivRank_eq (hf : IsSubmersion I J n f) (hn : n ≠ 0) (x : M) :
    mfderivRank I J f x = finrank 𝕜 F :=
  isRegularPoint_iff_mfderivRank_eq.mp ((hf.isSubmersionAt x).isRegularPoint hn)

end Manifold.IsSubmersion

variable {𝕜 : Type*} [RCLike 𝕜] {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n m : ℕ∞ω} {f : M → N} {r : ℕ}

namespace ContMDiff

variable [CompleteSpace F] [I.Boundaryless] [J.Boundaryless] [IsManifold I n M]
  [IsManifold J n N]

/-- **The kernel distribution of a map of constant rank.** For a `C^n` map `f` of constant rank
`r` between boundaryless manifolds, the source modelled on a finite-dimensional space `E`, the
kernels `ker (mfderiv f x)` form a `C^m` distribution of rank `dim E - r` when `m + 1 ≤ n`. -/
theorem isContMDiffDistribution_ker_mfderiv [IsManifold I 1 M] (hf : ContMDiff I J n f)
    (hmn : m + 1 ≤ n)
    (hr : ∀ x, mfderivRank I J f x = r) :
    IsContMDiffDistribution I m (finrank 𝕜 E - r) (fun x ↦ (mfderiv I J f x).ker) := by
  have hn : 1 ≤ n := le_add_self.trans hmn
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  refine isContMDiffDistribution_iff.2 fun x ↦ ?_
  obtain ⟨Φ, Ψ, hxΦ, -, -, -, hmap, hA⟩ :=
    hf.contMDiffOn.exists_partialDiffeomorph_comp_eq_mfderivModel_comp isOpen_univ (mem_univ x)
      hn fun y _ ↦ ((hr y).trans (hr x).symm).le
  -- The map reads as the linear map `A` in the coordinates `Φ` and `Ψ`.
  let A : E →L[𝕜] F := mfderivModel I J f x
  let K : Submodule 𝕜 E := LinearMap.ker (A : E →ₗ[𝕜] F)
  -- On the source of `Φ`, the kernels are the preimages of `ker A` under the derivative of `Φ`.
  have hker {y : M} (hy : y ∈ Φ.source) :
      (mfderiv I J f y).ker = K.comap (mfderiv I 𝓘(𝕜, E) Φ y).toLinearMap := by
    have h := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(𝕜, F))
      (hA.eventuallyEq_of_mem (Φ.open_source.mem_nhds hy))
    rw [mfderiv_comp y A.mdifferentiableAt (Φ.mdifferentiableAt hn0 hy),
      A.mfderiv_eq] at h
    rw [← (Ψ.isLocalDiffeomorphAt J 𝓘(𝕜, F) n (hmap hy)).ker_mfderiv_comp hn0
      (hf.mdifferentiableAt hn0), h]
    ext v
    -- The derivative of `A ∘ Φ` at `y` is `A ∘L mfderiv Φ y`, up to the identification
    -- `tangentSpaceCast` of tangent spaces of `F`.
    simp only [LinearMap.mem_ker, K, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply]
    exact (tangentSpaceCast _ _ _).map_eq_zero_iff
  -- The kernel of `A` has dimension `dim E - r`.
  have hK : finrank 𝕜 K = finrank 𝕜 E - r := by
    have h := finrank_ker_mfderiv_add_mfderivRank (I := I) (J := J) (f := f) (x := x)
    rw [hr x] at h
    rw [show K = _ from ker_mfderivModel I J f x, LinearEquiv.finrank_map_eq]
    omega
  have : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
  -- Pull back through `Φ` a constant frame of `K`.
  have hC := isContMDiffDistribution_const (n := m) K
  rw [hK] at hC
  obtain ⟨U, hU, hxU, X, hX⟩ := isContMDiffDistribution_iff.1 hC (Φ x)
  have hY := hX.comap_mfderivWithin Φ hmn
  refine ⟨Φ.source ∩ Φ ⁻¹' U, Φ.toOpenPartialHomeomorph.isOpen_inter_preimage hU,
    ⟨hxΦ, hxU⟩, _, ⟨hY.contMDiffOn, hY.linearIndependent, fun {y} hy ↦ ?_⟩⟩
  rw [hY.span_eq hy, hker hy.1, Φ.mfderivWithin_source hy.1]

end ContMDiff

namespace TauCeti.Foliation

variable [CompleteSpace F] [I.Boundaryless] [J.Boundaryless] [IsManifold I (n + 1) M]
  [IsManifold J (n + 1) N]

/-- **The kernel foliation of a map of constant rank.** For a `C^(n+1)` map `f` of constant rank
`r` between boundaryless manifolds, with `1 ≤ n`, the source modelled on a finite-dimensional
space `E`, the kernels `ker (mfderiv f x)` form a `C^n` foliation of rank `dim E - r`. -/
def ofConstantRank (hf : ContMDiff I J (n + 1) f) (hr : ∀ x, mfderivRank I J f x = r)
    (hn : 1 ≤ n) : Foliation I n M (finrank 𝕜 E - r) where
  one_le := hn
  distribution x := (mfderiv I J f x).ker
  isContMDiffDistribution := by
    have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    exact hf.isContMDiffDistribution_ker_mfderiv le_rfl hr
  isInvolutiveDistribution := by
    have h2 : minSmoothness 𝕜 2 ≤ n + 1 := by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact SymplecticGeometry.two_le_add_one_of_one_le hn
    -- `2 ≤ n + 1` holds only by `hn`, which instance search cannot use, so no instance lowers
    -- `IsManifold _ (n + 1) _`; going through `IsManifold _ 2 _` and
    -- `IsManifold.minSmoothness_of_isRCLikeNormedField` would need the same two `have`s.
    have : IsManifold I (minSmoothness 𝕜 2) M := .of_le h2
    have : IsManifold J (minSmoothness 𝕜 2) N := .of_le h2
    have : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
    exact hf.isInvolutiveDistribution_ker_mfderiv h2

/-- The tangent space at `x` of the kernel foliation of `f` is the kernel of `mfderiv f x`. -/
@[simp]
theorem ofConstantRank_distribution (hf : ContMDiff I J (n + 1) f)
    (hr : ∀ x, mfderivRank I J f x = r) (hn : 1 ≤ n) (x : M) :
    (ofConstantRank hf hr hn).distribution x = (mfderiv I J f x).ker :=
  (rfl)

end TauCeti.Foliation

namespace Manifold.IsSubmersion

/-- The fibres of a submersion: for a `C^(n+1)` submersion, `1 ≤ n`, the kernels of its derivative
form a `C^n` foliation of rank `dim E - dim F`. -/
example [CompleteSpace F] [FiniteDimensional 𝕜 F] [I.Boundaryless] [J.Boundaryless]
    [IsManifold I (n + 1) M] [IsManifold J (n + 1) N] (hf : IsSubmersion I J (n + 1) f)
    (hn : 1 ≤ n) : Foliation I n M (finrank 𝕜 E - finrank 𝕜 F) :=
  Foliation.ofConstantRank hf.contMDiff (hf.mfderivRank_eq (one_pos.trans_le le_add_self).ne') hn

end Manifold.IsSubmersion

namespace TauCeti.Foliation

open TauCeti.Manifold

variable {E F H G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I (n + 1) M] {f : M → N} {x y : M}

/-- A real map of constant rank is constant on each leaf of its kernel foliation. -/
theorem SameLeaf.apply_eq_of_ofConstantRank [FiniteDimensional ℝ E] [CompleteSpace F]
    [I.Boundaryless] [J.Boundaryless] [IsManifold J (n + 1) N] {r : ℕ}
    {hf : ContMDiff I J (n + 1) f} {hr : ∀ x, mfderivRank I J f x = r} {hn : 1 ≤ n}
    (h : (ofConstantRank hf hr hn).SameLeaf x y) : f x = f y :=
  have : IsManifold J 1 N := .of_le (n := n + 1) le_add_self
  h.apply_eq_of_le_ker (hf.mdifferentiable (one_pos.trans_le le_add_self).ne')
    fun x ↦ (ofConstantRank_distribution hf hr hn x).le

section Fibres

variable [FiniteDimensional ℝ E] [CompleteSpace F] [I.Boundaryless] [J.Boundaryless]
  [IsManifold J (n + 1) N] {r : ℕ}

/-- A curve, `C¹` on `[a, b]`, along which a map `f` of constant rank is constant stays in one
leaf of the kernel foliation of `f`. -/
theorem sameLeaf_ofConstantRank_of_eqOn (hf : ContMDiff I J (n + 1) f)
    (hr : ∀ x, mfderivRank I J f x = r) (hn : 1 ≤ n) {γ : ℝ → M} {a b s t : ℝ} {y : N}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) (hfγ : EqOn (f ∘ γ) (fun _ ↦ y) (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    (ofConstantRank hf hr hn).SameLeaf (γ s) (γ t) := by
  refine sameLeaf_of_contMDiffOn_of_tangent hγ (fun u hu ↦ ?_) hs ht
  rw [ofConstantRank_distribution, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  exact mfderiv_curveVelocityWithin_eq_zero_of_eqOn hfγ hu

/-- **Leaves are open in the fibres.** For a map `f` of constant rank, every point `y` of the
fibre of `f` through `x` that is close enough to `x` lies on the leaf of `x` of the kernel
foliation of `f`. -/
theorem eventually_sameLeaf_ofConstantRank (hf : ContMDiff I J (n + 1) f)
    (hr : ∀ x, mfderivRank I J f x = r) (hn : 1 ≤ n) (x : M) :
    ∀ᶠ y in 𝓝[f ⁻¹' {f x}] x, (ofConstantRank hf hr hn).SameLeaf x y := by
  have h1 : (1 : ℕ∞ω) ≤ n + 1 := le_add_self
  obtain ⟨φ, hxφ, -, hφx, -, hφi, hker⟩ :=
    hf.contMDiffOn.exists_openPartialHomeomorph_apply_eq_iff_mem_ker isOpen_univ (mem_univ x) h1
      fun y _ ↦ ((hr y).trans (hr x).symm).le
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 φ.open_target (φ x) (φ.map_source hxφ)
  have hV : φ.source ∩ φ ⁻¹' Metric.ball (φ x) ε ∈ 𝓝 x :=
    Filter.inter_mem (φ.open_source.mem_nhds hxφ)
      ((φ.continuousAt hxφ).preimage_mem_nhds (Metric.ball_mem_nhds _ hε))
  filter_upwards [mem_nhdsWithin_of_mem_nhds hV, self_mem_nhdsWithin] with y ⟨hyφ, hyb⟩ hfy
  -- The preimage under `φ` of the segment from `φ x = 0` to `φ y` is a curve in the fibre.
  have hseg : segment ℝ (φ x) (φ y) ⊆ φ.target :=
    ((convex_ball _ _).segment_subset (Metric.mem_ball_self hε) hyb).trans hball
  let ℓ : ℝ → E := AffineMap.lineMap (φ x) (φ y)
  have hℓ : MapsTo ℓ (Icc 0 1) φ.target := fun _ ht ↦ hseg (lineMap_mem_segment ℝ _ _ ht)
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (φ.symm ∘ ℓ) (Icc 0 1) := (hφi.comp_lineMap hseg).of_le h1
  have hfγ : EqOn (f ∘ φ.symm ∘ ℓ) (fun _ ↦ f x) (Icc 0 1) := fun t ht ↦ by
    refine (hker _ (φ.map_target (hℓ ht))).2 ?_
    rw [φ.right_inv (hℓ ht)]
    simp only [ℓ, AffineMap.lineMap_apply_module', hφx, sub_zero, add_zero, map_smul]
    exact Submodule.smul_mem _ t ((hker y hyφ).1 hfy)
  simpa [ℓ, φ.left_inv hxφ, φ.left_inv hyφ] using
    sameLeaf_ofConstantRank_of_eqOn hf hr hn hγ hfγ (left_mem_Icc.2 zero_le_one)
      (right_mem_Icc.2 zero_le_one)

/-- In a preconnected fibre of a map `f` of constant rank, any two points lie on one leaf of the
kernel foliation of `f`. -/
theorem sameLeaf_ofConstantRank_of_isPreconnected_preimage_singleton
    (hf : ContMDiff I J (n + 1) f) (hr : ∀ x, mfderivRank I J f x = r) (hn : 1 ≤ n) {b : N}
    (hb : IsPreconnected (f ⁻¹' {b})) (hx : f x = b) (hy : f y = b) :
    (ofConstantRank hf hr hn).SameLeaf x y :=
  hb.induction₂ (ofConstantRank hf hr hn).SameLeaf (fun z hz ↦ by
      rw [← mem_singleton_iff.1 (mem_preimage.1 hz)]
      exact eventually_sameLeaf_ofConstantRank hf hr hn z)
    (fun _ _ _ _ _ _ ↦ SameLeaf.trans) (fun _ _ _ _ ↦ SameLeaf.symm) hx hy

end Fibres

end TauCeti.Foliation

end
