/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ConstantRank.Basic
public import TauCeti.Geometry.Manifold.Distribution.Kernel
public import TauCeti.Geometry.Manifold.Foliation.Leaf
public import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Distribution.Diffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.RegularValue
import SymplecticGeometry.Geometry.Manifold.Foliation.Constancy

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
* `Manifold.IsSubmersion.mfderivRank_eq`: a submersion has constant rank `dim F`, so the fibres
  of a submersion give an example of the construction.

## Implementation notes

In the coordinates `φ`, `ψ` of Tau Ceti's rank theorem
`ContMDiffOn.exists_openPartialHomeomorph_comp_eq_mfderiv_comp` around a point `x`, the map reads
as the linear map `A` given by `mfderiv f x`. On the source of `φ`, the kernel of `mfderiv f y` is
the preimage under `mfderiv φ y` of the fixed subspace `ker A` (by Tau Ceti's
`IsLocalDiffeomorphAt.ker_mfderiv_comp` for `ψ`), so pulling back through `φ`, by
`TauCeti.IsDistributionFrameOn.comap_mfderivWithin`, a constant frame of `ker A` from
`TauCeti.isContMDiffDistribution_const` gives a local frame. This is the argument
of Tau Ceti's `Manifold.IsSubmersionAtOfComplement.isDistributionFrameOn_ker_mfderiv`, whose proof
the proof of `ContMDiff.isContMDiffDistribution_ker_mfderiv` adapts, with the rank theorem's
coordinates in place of the normal form of a submersion. Involutivity is Tau Ceti's
`ContMDiff.isInvolutiveDistribution_ker_mfderiv`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (the rank theorem) and Chapter 19 (distributions and foliations).
-/

public section

noncomputable section

open Set Function Module TauCeti
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
  isRegularPoint_iff_mfderivRank_eq.mp
    (isRegularPoint_iff.mpr ((hf.isSubmersionAt x).surjective_mfderiv hn))

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
  obtain ⟨φ, ψ, hxφ, -, -, hφ, hφi, -, hψ, hψi, hmap, hlin⟩ :=
    hf.contMDiffOn.exists_openPartialHomeomorph_comp_eq_mfderiv_comp isOpen_univ (mem_univ x) hn
      fun y _ ↦ ((hr y).trans (hr x).symm).le
  -- The map reads as the linear map `A` in the coordinates `φ` and `ψ`.
  let A : E →L[𝕜] F := (tangentSpaceCastModel J (f x) : TangentSpace J (f x) →L[𝕜] F) ∘L
    mfderiv I J f x ∘L ((tangentSpaceCastModel I x).symm : E →L[𝕜] TangentSpace I x)
  let K : Submodule 𝕜 E := LinearMap.ker (A : E →ₗ[𝕜] F)
  let Φ : PartialDiffeomorph I 𝓘(𝕜, E) M E n :=
    ⟨φ.toPartialEquiv, φ.open_source, φ.open_target, hφ, hφi⟩
  let Ψ : PartialDiffeomorph J 𝓘(𝕜, F) N F n :=
    ⟨ψ.toPartialEquiv, ψ.open_source, ψ.open_target, hψ, hψi⟩
  -- `hlin` is this equation with the composites unfolded, for the coercions of `φ` and `ψ`.
  have hA : EqOn (Ψ ∘ f) (A ∘ Φ) Φ.source := fun y hy ↦ hlin y hy
  -- On the source of `φ`, the kernels are the preimages of `ker A` under the derivative of `φ`.
  have hker {y : M} (hy : y ∈ Φ.source) :
      (mfderiv I J f y).ker = K.comap (mfderiv I 𝓘(𝕜, E) Φ y).toLinearMap := by
    have h := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(𝕜, F))
      (hA.eventuallyEq_of_mem (Φ.open_source.mem_nhds hy))
    rw [mfderiv_comp y A.mdifferentiableAt (Φ.mdifferentiableAt hn0 hy),
      A.mfderiv_eq] at h
    rw [← (Ψ.isLocalDiffeomorphAt J 𝓘(𝕜, F) n (hmap hy)).ker_mfderiv_comp hn0
      (hf.mdifferentiableAt hn0), h]
    ext v
    -- The derivative of `A ∘ φ` at `y` is `A ∘L mfderiv φ y`, up to the identification
    -- `tangentSpaceCast` of tangent spaces of `F`.
    simp only [LinearMap.mem_ker, K, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply]
    exact (tangentSpaceCast _ _ _).map_eq_zero_iff
  -- The kernel of `A` has dimension `dim E - r`.
  have hK : finrank 𝕜 K = finrank 𝕜 E - r := by
    have h := finrank_ker_mfderiv_add_mfderivRank (I := I) (J := J) (f := f) (x := x)
    rw [hr x] at h
    have hcomp : K = (mfderiv I J f x).ker.map
        ((tangentSpaceCastModel I x).toLinearEquiv : TangentSpace I x →ₗ[𝕜] E) := by
      ext v
      simp [K, A, Submodule.mem_map_equiv]
    rw [hcomp, LinearEquiv.finrank_map_eq]
    omega
  have : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
  -- Pull back through `φ` a constant frame of `K`.
  have hC := isContMDiffDistribution_const (n := m) K
  rw [hK] at hC
  obtain ⟨U, hU, hxU, X, hX⟩ := isContMDiffDistribution_iff.1 hC (φ x)
  have hY := hX.comap_mfderivWithin Φ hmn
  refine ⟨φ.source ∩ φ ⁻¹' U, φ.isOpen_inter_preimage hU, ⟨hxφ, hxU⟩, _,
    ⟨hY.contMDiffOn, hY.linearIndependent, fun {y} hy ↦ ?_⟩⟩
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
      rw [minSmoothness_of_isRCLikeNormedField, ← one_add_one_eq_two]
      exact add_le_add_left hn 1
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

end TauCeti.Foliation

end
