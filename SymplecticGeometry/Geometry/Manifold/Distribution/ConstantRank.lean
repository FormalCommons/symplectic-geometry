/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ConstantRank
public import TauCeti.Geometry.Manifold.Distribution.Kernel
public import TauCeti.Geometry.Manifold.Foliation.Leaf
public import TauCeti.Geometry.Manifold.Submersion.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorField.Pullback
import TauCeti.Geometry.Manifold.RegularValue
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Constancy

/-!
# The kernel foliation of a map of constant rank

Let `f : M → N` be a smooth map of constant rank `r` between boundaryless manifolds, the source
modelled on a finite-dimensional space `E`. The kernels of its derivative form a smooth
distribution of rank `dim E - r`, and, being involutive, a foliation of `M`. Over `ℝ`, where
Tau Ceti defines the leaves of a foliation, each leaf lies in a fibre of `f`.

## Main results

* `MDifferentiableAt.mem_ker_mfderiv_iff_of_eventuallyEq`: where `f` reads as a linear map `A`
  in coordinates, the kernel of its derivative is the preimage of `ker A`.
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
the preimage under `mfderiv φ y` of the fixed subspace `ker A`, so the pullbacks through `φ` of
the constant vector fields given by a basis of `ker A` form a local frame. This is the argument
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

open Set Function Module VectorField TauCeti
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

namespace MDifferentiableAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {f : M → N} {y : M}

/-- If near `y` the map `f` reads as a continuous linear map `A` in coordinates `φ` and `ψ`
(`ψ ∘ f = A ∘ φ`), where `ψ` has invertible derivative at `f y`, then a tangent vector at `y`
lies in the kernel of the derivative of `f` exactly when `A` kills its image under the
derivative of `φ`. -/
theorem mem_ker_mfderiv_iff_of_eventuallyEq {φ : M → E} {ψ : N → F} {A : E →L[𝕜] F}
    (hA : ψ ∘ f =ᶠ[𝓝 y] A ∘ φ) (hf : MDifferentiableAt I J f y)
    (hφ : MDifferentiableAt I 𝓘(𝕜, E) φ y) (hψ : (mfderiv J 𝓘(𝕜, F) ψ (f y)).IsInvertible)
    (v : TangentSpace I y) :
    v ∈ (mfderiv I J f y).ker ↔ A (mfderiv I 𝓘(𝕜, E) φ y v) = 0 := by
  have h := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(𝕜, F)) hA
  rw [mfderiv_comp y (mdifferentiableAt_of_isInvertible_mfderiv hψ) hf,
    mfderiv_comp y A.mdifferentiableAt hφ, A.mfderiv_eq] at h
  obtain ⟨e, he⟩ := hψ
  -- Both sides of `h` applied to `v`; the composites unfold to these applications.
  have hv : mfderiv J 𝓘(𝕜, F) ψ (f y) (mfderiv I J f y v) =
      tangentSpaceCast 𝓘(𝕜, F) ((A ∘ φ) y) ((ψ ∘ f) y) (A (mfderiv I 𝓘(𝕜, E) φ y v)) :=
    congr($h v)
  have he' : mfderiv J 𝓘(𝕜, F) ψ (f y) (mfderiv I J f y v) = e (mfderiv I J f y v) := by
    rw [← he, ContinuousLinearEquiv.coe_coe]
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ← e.map_eq_zero_iff, ← he', hv]
  exact (tangentSpaceCast _ _ _).map_eq_zero_iff

end MDifferentiableAt

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
  -- `hlin` is this equation with the composites unfolded.
  have hA : EqOn (ψ ∘ f) (A ∘ φ) φ.source := fun y hy ↦ hlin y hy
  let K : Submodule 𝕜 E := LinearMap.ker (A : E →ₗ[𝕜] F)
  let Φ : PartialDiffeomorph I 𝓘(𝕜, E) M E n :=
    ⟨φ.toPartialEquiv, φ.open_source, φ.open_target, hφ, hφi⟩
  let Ψ : PartialDiffeomorph J 𝓘(𝕜, F) N F n :=
    ⟨ψ.toPartialEquiv, ψ.open_source, ψ.open_target, hψ, hψi⟩
  have hdφ {y : M} (hy : y ∈ φ.source) : (mfderiv I 𝓘(𝕜, E) φ y).IsInvertible :=
    (Φ.isLocalDiffeomorphAt I 𝓘(𝕜, E) n hy).isInvertible_mfderiv hn0
  -- On the source of `φ`, the kernels are the preimages of `ker A` under the derivative of `φ`.
  have hker {y : M} (hy : y ∈ φ.source) (v : TangentSpace I y) :
      v ∈ (mfderiv I J f y).ker ↔ mfderiv I 𝓘(𝕜, E) φ y v ∈ K := by
    have hψ : (mfderiv J 𝓘(𝕜, F) ψ (f y)).IsInvertible :=
      (Ψ.isLocalDiffeomorphAt J 𝓘(𝕜, F) n (hmap hy)).isInvertible_mfderiv hn0
    exact MDifferentiableAt.mem_ker_mfderiv_iff_of_eventuallyEq
      (hA.eventuallyEq_of_mem (φ.open_source.mem_nhds hy)) (hf.mdifferentiableAt hn0)
      (Φ.mdifferentiableAt hn0 hy) hψ v
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
  let b : Basis (Fin (finrank 𝕜 E - r)) 𝕜 K := (Module.finBasis 𝕜 _).reindex (finCongr hK)
  refine ⟨φ.source, φ.open_source, hxφ,
    fun i ↦ mpullback I 𝓘(𝕜, E) φ (fun z ↦ ((b i : E) : TangentSpace 𝓘(𝕜, E) z)),
    ⟨fun i y hy ↦ ?_, fun {y} hy ↦ ?_, fun {y} hy ↦ ?_⟩⟩
  · exact ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin (t := univ)
      (contMDiffAt_vectorSpace_iff_contDiffAt.2 contDiffAt_const).contMDiffWithinAt
      ((hφ y hy).contMDiffAt (φ.open_source.mem_nhds hy)) (hdφ hy) hmn (by simp)
  all_goals
    obtain ⟨e, he⟩ := hdφ hy
    have hinv : (mfderiv I 𝓘(𝕜, E) φ y).inverse = e.symm := by
      rw [← he, ContinuousLinearMap.inverse_equiv]
    have hX (i : Fin (finrank 𝕜 E - r)) : mpullback I 𝓘(𝕜, E) φ
        (fun z ↦ ((b i : E) : TangentSpace 𝓘(𝕜, E) z)) y = e.symm (b i : E) :=
      mpullback_apply.trans (congrArg (· (b i : E)) hinv)
    have hli : LinearIndependent 𝕜 fun i ↦ e.symm (b i : E) :=
      (b.linearIndependent.map' K.subtype K.ker_subtype).map'
        e.symm.toLinearMap (LinearMap.ker_eq_bot.2 e.symm.injective)
    simp only [hX]
  · exact hli
  · -- The values span a subspace of the kernel of the same dimension.
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, hker hy, ← he, ContinuousLinearEquiv.coe_coe]
      exact (e.apply_symm_apply (b i : E)).symm ▸ (b i).property
    · have h := finrank_ker_mfderiv_add_mfderivRank (I := I) (J := J) (f := f) (x := y)
      rw [hr y] at h
      rw [finrank_span_eq_card hli, Fintype.card_fin]
      omega

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

variable {E F H G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I (n + 1) M] [IsManifold J (n + 1) N] {f : M → N} {r : ℕ}

/-- A real map of constant rank is constant on each leaf of its kernel foliation. -/
theorem SameLeaf.apply_eq_of_ofConstantRank {hf : ContMDiff I J (n + 1) f}
    {hr : ∀ x, mfderivRank I J f x = r} {hn : 1 ≤ n} {x y : M}
    (h : (ofConstantRank hf hr hn).SameLeaf x y) : f x = f y := by
  have : IsManifold J 1 N := IsManifold.of_le (I := J) (n := n + 1) le_add_self
  refine sameLeaf_le (r := fun x y ↦ f x = f y) ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩
    (fun x y hxy ↦ ?_) x y h
  -- Along a curve tangent to the kernels, the derivative of `f ∘ γ` vanishes.
  obtain ⟨γ, hγ, htan, rfl, rfl⟩ := joinedByTangentCurve_iff.mp hxy
  refine Convex.apply_eq_of_hasMFDerivWithinAt_zero (J := J) (g := f ∘ γ) (convex_Icc 0 1)
    (fun t ht ↦ ?_) (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  have hft : MDifferentiableAt I J f (γ t) :=
    hf.mdifferentiableAt (one_pos.trans_le le_add_self).ne'
  have hγt := hγ.mdifferentiableOn one_ne_zero t ht
  have hv := htan t ht
  rw [ofConstantRank_distribution, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
  have hd := hasMFDerivWithinAt_curveVelocityWithin (hft.comp_mdifferentiableWithinAt t hγt)
  rwa [curveVelocityWithin_map hft (uniqueDiffOn_Icc zero_lt_one t ht) hγt, hv,
    ContinuousLinearMap.smulRight_zero] at hd

end TauCeti.Foliation

end
