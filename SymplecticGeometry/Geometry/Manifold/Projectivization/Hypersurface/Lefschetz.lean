/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.Veronese
public import TauCeti.Geometry.Manifold.Projectivization.Lefschetz
public import TauCeti.Topology.Homotopy.HomotopyGroup.ConnectedMap.Basic
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact
import TauCeti.Topology.ComplexProjectiveSpace.Projectivization

/-!
# The Lefschetz hyperplane theorems for smooth projective hypersurfaces

Let `X ⊆ ℂℙⁿ⁺¹` be a smooth projective hypersurface of degree `d ≠ 0`. The inclusion
`X → ℂℙⁿ⁺¹` is `n`-connected: it induces bijections `π_k(X) → π_k(ℂℙⁿ⁺¹)` for `k < n` and a
surjection for `k = n`, and isomorphisms on singular homology `H_k(X; R) → H_k(ℂℙⁿ⁺¹; R)` for
`k < n`, with coefficients in any object `R` of an abelian category with coproducts. Hence `X` is
connected for `n ≠ 0` and simply connected for `2 ≤ n`.

These are Tau Ceti's Lefschetz theorems (`TauCeti.bijective_homotopyGroupMap_notMem_affineOpen`,
`TauCeti.surjective_homotopyGroupMap_notMem_affineOpen`,
`TauCeti.isIso_homologyMap_notMem_affineOpen`), applied to the hyperplane section `X` of its
image `Y` under the Veronese embedding as set up in `Hypersurface/Veronese.lean`
(`SmoothProjectiveHypersurface.exists_homotopyEquiv_nhds` and the manifold structure on the
affine part of `Y`), and carried back to `X ⊆ ℂℙⁿ⁺¹` along the
homeomorphisms `veroneseHyperplaneHomeomorph` and `veroneseHomeomorph`.

## Main results

* `SymplecticGeometry.SmoothProjectiveHypersurface.isNConnected_subtypeVal`: the inclusion is
  `n`-connected.
* `SymplecticGeometry.SmoothProjectiveHypersurface.bijective_homotopyGroupMap_subtypeVal` and
  `isIso_homologyMap_subtypeVal`: the inclusion induces bijections on `π_k` and isomorphisms on
  `H_k` for `k < n`.
* `SymplecticGeometry.SmoothProjectiveHypersurface.connectedSpace` (`n ≠ 0`) and
  `simplyConnectedSpace` (`2 ≤ n`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton (1963), §7.
* [A. Andreotti, T. Frankel, *The Lefschetz theorem on hyperplane sections*][AndreottiFrankel1959].
-/

public section

open CategoryTheory Limits Function Set Projectivization TauCeti
open scoped LinearAlgebra.Projectivization

namespace SymplecticGeometry

namespace SmoothProjectiveHypersurface

variable {n d : ℕ} (X : SmoothProjectiveHypersurface n d)

/-- The square relating the inclusion of `X` into `ℂℙⁿ⁺¹` to the inclusion of the hyperplane
section `Y ∩ {x₀ = 0}` into the Veronese image `Y`. -/
theorem veroneseHomeomorph_comp_subtypeVal [NeZero d] :
    (X.veroneseHomeomorph : C(ℙ ℂ (Fin (n + 2) → ℂ), X.veroneseImage)).comp
        (ContinuousMap.subtypeVal X.carrier) =
      (ContinuousMap.subtypeVal {y : X.veroneseImage |
        (y : ℙ ℂ (Fin (veroneseDim (n + 2) d - 1 + 1) → ℂ)) ∉ affineOpen 0}).comp
        (X.veroneseHyperplaneHomeomorph : C(X, {y : X.veroneseImage |
          (y : ℙ ℂ (Fin (veroneseDim (n + 2) d - 1 + 1) → ℂ)) ∉ affineOpen 0})) :=
  ContinuousMap.ext fun _ ↦ by simp

/-- **The Lefschetz hyperplane theorem in homotopy, for hypersurfaces.** For `d ≠ 0`, the
inclusion of a smooth hypersurface `X ⊆ ℂℙⁿ⁺¹` is `n`-connected: it induces injections
`π_k(X) → π_k(ℂℙⁿ⁺¹)` for `k < n` and surjections for `k ≤ n`, and every point of `ℂℙⁿ⁺¹` is
joined to a point of `X`. -/
theorem isNConnected_subtypeVal (hd : d ≠ 0) :
    (ContinuousMap.subtypeVal X.carrier).IsNConnected n := by
  have : NeZero d := ⟨hd⟩
  obtain ⟨W, hAW, hW_nhds, e, he⟩ := X.exists_homotopyEquiv_nhds
  have hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence :=
    he ▸ e.isWeakHomotopyEquivalence
  rw [← X.veroneseHyperplaneHomeomorph.isWeakHomotopyEquivalence.isNConnected_iff_of_comp_eq
    X.veroneseHomeomorph.isWeakHomotopyEquivalence X.veroneseHomeomorph_comp_subtypeVal]
  refine ⟨fun y ↦ ?_, fun k hk a ↦ ?_, fun k hk a ↦ ?_⟩
  · -- `Y` is path-connected, as `ℂℙⁿ⁺¹` is, and the hyperplane section is not empty.
    obtain ⟨x⟩ := X.nonempty hd
    refine ⟨X.veroneseHyperplaneHomeomorph x, ?_⟩
    have h := (PathConnectedSpace.joined (x : ℙ ℂ (Fin (n + 2) → ℂ))
      (X.veroneseHomeomorph.symm y)).map X.veroneseHomeomorph.continuous
    simpa using h
  · exact (bijective_homotopyGroupMap_notMem_affineOpen X.isClosed_veroneseImage 0
      X.veroneseAffine_def.symm (X.contMDiff_coe_veroneseAffine _)
      X.injective_mfderiv_coe_veroneseAffine hW hW_nhds
      (by simpa [Module.finrank_fin_fun] using hk) a).injective
  · exact surjective_homotopyGroupMap_notMem_affineOpen X.isClosed_veroneseImage 0
      X.veroneseAffine_def.symm (X.contMDiff_coe_veroneseAffine _)
      X.injective_mfderiv_coe_veroneseAffine hW hW_nhds
      (by simpa [Module.finrank_fin_fun, Nat.lt_succ_iff] using hk) a

/-- For `d ≠ 0`, the inclusion of a smooth hypersurface `X ⊆ ℂℙⁿ⁺¹` induces a bijection
`π_k(X, x) → π_k(ℂℙⁿ⁺¹, x)` for `k < n`, at every point `x` of `X`. Here `π_k` is indexed by
any finite type `J` of `k` cube directions. -/
theorem bijective_homotopyGroupMap_subtypeVal (hd : d ≠ 0) {J : Type*} [Finite J]
    (hJ : Nat.card J < n) (x : X) :
    Bijective (HomotopyGroup.map (N := J) (ContinuousMap.subtypeVal X.carrier)
      (rfl : (x : ℙ ℂ (Fin (n + 2) → ℂ)) = x)) :=
  ⟨(X.isNConnected_subtypeVal hd).map_injective J hJ x,
    (X.isNConnected_subtypeVal hd).map_surjective J hJ.le x⟩

/-- **The Lefschetz hyperplane theorem in homology, for hypersurfaces.** For `d ≠ 0`, the
inclusion of a smooth hypersurface `X ⊆ ℂℙⁿ⁺¹` induces isomorphisms on singular homology
`H_k(X; R) → H_k(ℂℙⁿ⁺¹; R)` for `k < n`, with coefficients in any object `R` of an abelian
category with coproducts. -/
theorem isIso_homologyMap_subtypeVal (hd : d ≠ 0) {C : Type*} [Category* C] [Abelian C]
    [HasCoproducts.{0} C] (R : C) {k : ℕ} (hk : k < n) :
    IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.subtypeVal X.carrier))) R k) := by
  have : NeZero d := ⟨hd⟩
  obtain ⟨W, hAW, hW_nhds, e, he⟩ := X.exists_homotopyEquiv_nhds
  have hW : IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.inclusion hAW))) R k) :=
    he ▸ e.isIso_homologyMap R k
  have hj := isIso_homologyMap_notMem_affineOpen X.isClosed_veroneseImage 0
    X.veroneseAffine_def.symm (X.contMDiff_coe_veroneseAffine _)
    X.injective_mfderiv_coe_veroneseAffine R hW hW_nhds
    (by simpa [Module.finrank_fin_fun] using hk)
  have hf := X.veroneseHyperplaneHomeomorph.toHomotopyEquiv.isIso_homologyMap R k
  -- The map of the homotopy equivalence of a homeomorphism is the homeomorphism itself.
  have hg : IsIso (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
      (X.veroneseHomeomorph : C(ℙ ℂ (Fin (n + 2) → ℂ), X.veroneseImage)))) R k) :=
    X.veroneseHomeomorph.toHomotopyEquiv.isIso_homologyMap R k
  -- Homology turns the square `veroneseHomeomorph_comp_subtypeVal` into a commutative square.
  have hsq := congrArg (fun f ↦ SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f)) R k)
    X.veroneseHomeomorph_comp_subtypeVal
  simp only [TopCat.ofHom_comp, Functor.map_comp, SSet.homologyMap_comp] at hsq
  have : IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.subtypeVal X.carrier))) R k ≫
        SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
          (X.veroneseHomeomorph : C(ℙ ℂ (Fin (n + 2) → ℂ), X.veroneseImage)))) R k) := by
    rw [hsq]
    exact IsIso.comp_isIso' hf hj
  exact IsIso.of_isIso_comp_right _ (SSet.homologyMap (TopCat.toSSet.map
    (TopCat.ofHom (X.veroneseHomeomorph : C(ℙ ℂ (Fin (n + 2) → ℂ), X.veroneseImage)))) R k)

/-- For `d ≠ 0` and `n ≠ 0`, a smooth hypersurface `X ⊆ ℂℙⁿ⁺¹` is path-connected. -/
theorem pathConnectedSpace (hd : d ≠ 0) (hn : n ≠ 0) : PathConnectedSpace X := by
  have h := (X.isNConnected_subtypeVal hd).injective 0 (Nat.pos_of_ne_zero hn)
  have := X.nonempty hd
  exact ⟨inferInstance, fun a b ↦ (ContinuousMap.joined_iff_of_injective_homotopyGroupMap _ (h a)).1
    (PathConnectedSpace.joined _ _)⟩

/-- For `d ≠ 0` and `n ≠ 0`, a smooth hypersurface `X ⊆ ℂℙⁿ⁺¹` is connected. -/
theorem connectedSpace (hd : d ≠ 0) (hn : n ≠ 0) : ConnectedSpace X :=
  have := X.pathConnectedSpace hd hn
  inferInstance

/-- For `d ≠ 0` and `2 ≤ n`, a smooth hypersurface `X ⊆ ℂℙⁿ⁺¹` is simply connected, as
`ℂℙⁿ⁺¹` is. -/
theorem simplyConnectedSpace (hd : d ≠ 0) (hn : 2 ≤ n) : SimplyConnectedSpace X := by
  have : SimplyConnectedSpace (ℙ ℂ (Fin (n + 2) → ℂ)) :=
    (ComplexProjectiveSpace.homeomorphProjectivization (n + 1)).toHomotopyEquiv
      |>.simplyConnectedSpace_iff.1 inferInstance
  exact ((X.isNConnected_subtypeVal hd).simplyConnectedSpace_iff hn).2 this

end SmoothProjectiveHypersurface

end SymplecticGeometry

end
