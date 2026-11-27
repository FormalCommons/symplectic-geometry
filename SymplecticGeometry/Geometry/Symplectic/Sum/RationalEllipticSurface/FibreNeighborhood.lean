/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Sum.RationalEllipticSurface.AffineCoordinate
import SymplecticGeometry.Geometry.Manifold.IsManifold.SecondCountable
import SymplecticGeometry.Geometry.Manifold.RegularValue.RestrictPreimage
import SymplecticGeometry.Geometry.Manifold.Submersion.RadialTrivialization
import SymplecticGeometry.Topology.FiberBundle.Trivialization
import TauCeti.Geometry.Manifold.RegularValue.Open
import TauCeti.Topology.Category.TopCat.Fiber
import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# A product neighbourhood of the fibre of `E(1)` adapted to the affine coordinate

The fibre of the rational elliptic surface over `[1 : 0] ∈ ℂℙ¹` is the image of the Fermat cubic
under `SymplecticGeometry.rationalEllipticSurface.fibreEmbedding`. This file builds a product
neighbourhood of it on which the second coordinate is the affine coordinate `t / s` of the
projection to `ℂℙ¹`: an open embedding `f` of the product of the Fermat cubic with a disc
`ball 0 ε` into the surface, with `f (x, 0)` the point `x` of the fibre and
`affineCoordinate (f (x, w)) = w`
(`SymplecticGeometry.rationalEllipticSurface.exists_isOpenEmbedding_prod_ball`).

## Proof

This is Ehresmann's fibration theorem for the affine coordinate near the fibre. On the open set
`SymplecticGeometry.rationalEllipticSurface.overAffineOpen` of points over the affine open
`s ≠ 0`, the affine coordinate is a smooth proper map to `ℂ`
(`SymplecticGeometry.rationalEllipticSurface.isProperMap_affineCoordinate_comp_subtypeVal`), and
`0` is a regular value of it, because the affine coordinate is regular along the fibre
(`SymplecticGeometry.rationalEllipticSurface.isRegularPoint_restrictScalars_affineCoordinate`).
The regular values of a closed map form an open set
(`TauCeti.isOpen_setOf_isRegularValue_of_isClosedMap`), so over some disc around `0` the affine
coordinate is a smooth proper submersion, and it is locally trivial over a neighbourhood of `0`
(`Manifold.IsSubmersion.exists_trivialization_of_isProperMap`), with the fibre over `0` as model
fibre. This fibre is the Fermat cubic
(`SymplecticGeometry.rationalEllipticSurface.fibreHomeomorph`,
`ContinuousMap.preimageSingletonHomeomorphFiber`). The inverse of the trivialization, over a
smaller disc and read through the identification of the fibre over `0` with the model fibre
(`Bundle.Trivialization.mapFiberHomeomorph`), is the product neighbourhood. The restriction to a
disc of regular values follows the proof of `ContMDiff.nonempty_diffeomorph_fiber_of_isProperMap`.

## References

* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1 and §7.2.
-/

public section

open Set TauCeti Projectivization Metric TopologicalSpace
open scoped ContDiff Manifold LinearAlgebra.Projectivization ComplexManifold

namespace SymplecticGeometry.rationalEllipticSurface

/-- **A product neighbourhood of the fibre of `E(1)` over `[1 : 0]` adapted to the affine
coordinate.** For some `ε > 0` there is an open embedding `f` of the product of the Fermat cubic
with the disc `ball 0 ε` into the rational elliptic surface that sends `(x, 0)` to the point
`x` of the fibre over `[1 : 0]`, and whose image lies over the affine open `s ≠ 0` of `ℂℙ¹`, with
affine coordinate `affineCoordinate (f (x, w)) = w`. -/
theorem exists_isOpenEmbedding_prod_ball :
    ∃ (ε : ℝ) (hε : 0 < ε) (f : SmoothProjectiveHypersurface.fermat 1 3 × ball (0 : ℂ) ε →
        rationalEllipticSurface), Topology.IsOpenEmbedding f ∧
      (∀ x, f (x, ⟨0, mem_ball_self hε⟩) = fibreEmbedding x) ∧
      ∀ p, affineCoordinate (f p) = p.2 ∧
        (f p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 ∈ affineOpen 0 := by
  rcases isEmpty_or_nonempty (SmoothProjectiveHypersurface.fermat 1 3) with hX | ⟨⟨x₀⟩⟩
  · -- Over an empty cubic there is nothing to embed.
    exact ⟨1, one_pos, fun p ↦ isEmptyElim p.1, .of_isEmpty _, fun x ↦ isEmptyElim x,
      fun p ↦ isEmptyElim p.1⟩
  set M := overAffineOpen
  set a : M → ℂ := affineCoordinate ∘ Subtype.val
  have ha : ContMDiff 𝓘(ℝ, Fin 2 → ℂ) 𝓘(ℝ, ℂ) ∞ a := contMDiff_affineCoordinate_comp_subtypeVal
  have hap : IsProperMap a := isProperMap_affineCoordinate_comp_subtypeVal
  -- A disc `ball 0 ε` of regular values, over which the affine coordinate is a proper submersion.
  obtain ⟨ε, hε, hεreg⟩ := Metric.isOpen_iff.1
    (isOpen_setOf_isRegularValue_of_isClosedMap ha (by simp) hap.isClosedMap) 0
    isRegularValue_affineCoordinate_comp_subtypeVal_zero
  set R : Opens ℂ := ⟨ball 0 ε, isOpen_ball⟩
  set P : Opens M := ⟨a ⁻¹' R, R.isOpen.preimage ha.continuous⟩
  set g : P → R := (R : Set ℂ).restrictPreimage a
  have hg : Manifold.IsSubmersion 𝓘(ℝ, Fin 2 → ℂ) 𝓘(ℝ, ℂ) ∞ g :=
    ((ha.restrictPreimage R).isSubmersionOfComplement_of_surjective_mfderiv (by simp)
      fun p ↦ isRegularPoint_iff.1 ((isRegularPoint_restrictPreimage_iff ha.continuous R).2
        (isRegularValue_iff.1 (hεreg p.property) p rfl))).isSubmersion
  have := 𝓘(ℝ, Fin 2 → ℂ).secondCountableTopology_of_sigmaCompact rationalEllipticSurface
  have := ChartedSpace.locallyCompactSpace (Fin 2 → ℂ) P
  -- The Fermat cubic is the fibre of `g` over `0`.
  set b₀ : R := ⟨0, mem_ball_self hε⟩
  set κ : SmoothProjectiveHypersurface.fermat 1 3 ≃ₜ MapFiber g b₀ :=
    fibreHomeomorph.trans
      (ContinuousMap.preimageSingletonHomeomorphFiber (p := ⟨a, ha.continuous⟩) b₀.property)
  -- A trivialization of `g` around `0`, and a disc `ball 0 δ` inside its base set.
  obtain ⟨e, hb₀e, -, -⟩ := hg.exists_trivialization_of_isProperMap (hap.restrictPreimage _)
    ⟨(κ x₀).val, (κ x₀).property⟩
  obtain ⟨δ, hδ, hδe⟩ := Metric.isOpen_iff.1
    (R.isOpen.isOpenMap_subtypeVal _ e.open_baseSet) 0 ⟨b₀, hb₀e, rfl⟩
  set ι : ball (0 : ℂ) δ → R := fun w ↦
    ⟨w, by obtain ⟨b, -, hb⟩ := hδe w.property; exact hb ▸ b.property⟩
  have hιe (w : ball (0 : ℂ) δ) : ι w ∈ e.baseSet := by
    obtain ⟨b, hb, hbw⟩ := hδe w.property
    rwa [show ι w = b from Subtype.ext hbw.symm]
  have hι : Topology.IsOpenEmbedding ι :=
    (Topology.IsOpenEmbedding.of_comp_iff ι R.isOpen.isOpenEmbedding_subtypeVal).1
      isOpen_ball.isOpenEmbedding_subtypeVal
  set ψ := κ.trans (e.mapFiberHomeomorph hb₀e)
  set j : SmoothProjectiveHypersurface.fermat 1 3 × ball (0 : ℂ) δ → R × MapFiber g b₀ :=
    fun p ↦ (ι p.2, ψ p.1)
  have hj : Topology.IsOpenEmbedding j :=
    (hι.prodMap ψ.isOpenEmbedding).comp (Homeomorph.prodComm _ _).isOpenEmbedding
  -- The inverse of the trivialization over the small disc.
  have hs : Topology.IsOpenEmbedding (e.toOpenPartialHomeomorph.symm ∘ j) :=
    e.toOpenPartialHomeomorph.symm.isOpenEmbedding_comp hj
      (range_subset_iff.2 fun p ↦ e.mem_target.2 (hιe p.2))
  refine ⟨δ, hδ, fun p ↦ (e.toOpenPartialHomeomorph.symm (j p)).val.val,
    M.isOpen.isOpenEmbedding_subtypeVal.comp (P.isOpen.isOpenEmbedding_subtypeVal.comp hs),
    fun x ↦ ?_, fun p ↦ ⟨congrArg Subtype.val (e.proj_symm_apply' (hιe p.2)),
      mem_overAffineOpen.1 (e.toOpenPartialHomeomorph.symm (j p)).val.property⟩⟩
  have h := congrArg Subtype.val ((e.mapFiberHomeomorph hb₀e).symm_apply_apply (κ x))
  rw [Bundle.Trivialization.mapFiberHomeomorph_symm_apply] at h
  refine (congrArg (fun z : P ↦ z.val.val) h).trans ?_
  -- The points of `P` are those of `a ⁻¹' R`, the domain of `g`, as sets of points of `M`.
  exact (congrArg Subtype.val (ContinuousMap.coe_coe_preimageSingletonHomeomorphFiber_apply
    (p := ⟨a, ha.continuous⟩) b₀.property _)).trans
    (coe_coe_fibreHomeomorph_apply x)

end SymplecticGeometry.rationalEllipticSurface

end
