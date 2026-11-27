/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Sum.RationalEllipticSurface.AffineCoordinate
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import SymplecticGeometry.Geometry.Manifold.IsManifold.SecondCountable
import SymplecticGeometry.Geometry.Manifold.RegularValue.CriticalSet
import SymplecticGeometry.Geometry.Manifold.RegularValue.RestrictPreimage
import SymplecticGeometry.Geometry.Manifold.Submersion.RadialTrivialization
import SymplecticGeometry.Topology.FiberBundle.Trivialization
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
`M` of points over the affine open `s ≠ 0`, the affine coordinate is a smooth proper map `M → ℂ`:
the points of `M` with affine coordinate in a compact set `K` are those over the image of `K`
under the inverse of the affine chart, a closed subset of the compact surface. Its critical set is
closed, so its image is closed, and it misses `0` because the affine coordinate is regular
along the fibre
(`SymplecticGeometry.rationalEllipticSurface.isRegularPoint_restrictScalars_affineCoordinate`).
Over a disc around `0` free of critical values, the affine coordinate is a smooth proper
submersion, so it is locally trivial over a neighbourhood of `0`
(`Manifold.IsSubmersion.exists_trivialization_of_isProperMap`), with the fibre over `0` as model
fibre, and this fibre is the Fermat cubic
(`SymplecticGeometry.rationalEllipticSurface.mem_range_fibreEmbedding_iff`). The inverse of the
trivialization, over a smaller disc and read through the identification of the fibre over `0`
with the model fibre (`Bundle.Trivialization.mapFiberHomeomorph`), is the product
neighbourhood. The restriction to a disc of regular values follows the proof of
`ContMDiff.nonempty_diffeomorph_fiber_of_isProperMap`.

## References

* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1 and §7.2.
-/

public section

open Set TauCeti Projectivization Metric TopologicalSpace
open scoped ContDiff Manifold LinearAlgebra.Projectivization ComplexManifold

namespace SymplecticGeometry.rationalEllipticSurface

/-- The open set of points of the rational elliptic surface over the affine open `s ≠ 0` of
`ℂℙ¹`. -/
private def overAffineOpen : Opens rationalEllipticSurface :=
  ⟨{p | (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 ∈ affineOpen 0},
    (isOpen_affineOpen 0).preimage (continuous_snd.comp continuous_subtypeVal)⟩

/-- Membership in `overAffineOpen`. -/
private theorem mem_overAffineOpen {p : rationalEllipticSurface} :
    p ∈ overAffineOpen ↔ (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 ∈ affineOpen 0 :=
  Iff.rfl

/-- The affine coordinate is a proper map on the points over the affine open `s ≠ 0`. -/
private theorem isProperMap_affineCoordinate_overAffineOpen :
    IsProperMap (affineCoordinate ∘ Subtype.val : overAffineOpen → ℂ) := by
  refine isProperMap_iff_isCompact_preimage.2 ⟨?_, fun K hK ↦ ?_⟩
  · refine continuous_iff_continuousAt.2 fun p ↦ ?_
    exact ((contMDiffAt_affineCoordinate (mem_overAffineOpen.1 p.property) 0).continuousAt).comp
      continuous_subtypeVal.continuousAt
  -- The preimage of `K` is the set of points over the image of `K` under the inverse chart.
  set T : Set (ℙ ℂ (Fin 2 → ℂ)) := (fun z : ℂ ↦ (affineChart 0).symm fun _ ↦ z) '' K
  have hT : IsCompact T :=
    hK.image ((continuous_affineChart_symm 0).comp (continuous_pi fun _ ↦ continuous_id))
  set S : Set rationalEllipticSurface := {p | (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 ∈ T}
  have hS : IsCompact S :=
    (hT.isClosed.preimage (continuous_snd.comp continuous_subtypeVal)).isCompact
  have hST : S ⊆ range (Subtype.val : overAffineOpen → rationalEllipticSurface) := by
    rintro p ⟨z, -, hz⟩
    refine ⟨⟨p, mem_overAffineOpen.2 ?_⟩, rfl⟩
    rw [← hz, ← affineChart_source, ← (affineChart 0).symm_target]
    exact (affineChart 0).symm.map_source (by simp)
  have hpre : (affineCoordinate ∘ Subtype.val : overAffineOpen → ℂ) ⁻¹' K =
      Subtype.val ⁻¹' S := by
    ext p
    refine ⟨fun hp ↦ ⟨_, hp,
      (snd_eq_affineChart_symm_affineCoordinate (mem_overAffineOpen.1 p.property)).symm⟩, ?_⟩
    rintro ⟨z, hz, hpz⟩
    have h : affineCoordinate p.val = z := by
      rw [affineCoordinate_def, ← hpz, (affineChart 0).right_inv (by simp)]
    simpa [h] using hz
  rw [hpre]
  exact (Topology.IsInducing.subtypeVal.isCompact_preimage_iff hST).2 hS

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
  have ha : ContMDiff 𝓘(ℝ, Fin 2 → ℂ) 𝓘(ℝ, ℂ) ∞ a := fun p ↦
    ((contMDiffAt_affineCoordinate (mem_overAffineOpen.1 p.property) ∞).restrictScalars' ℝ).comp p
      (contMDiff_subtypeVal p)
  have hap : IsProperMap a := isProperMap_affineCoordinate_overAffineOpen
  -- The affine coordinate is regular along the fibre, so `0` is not a critical value.
  have hC : IsClosed (a '' criticalSet 𝓘(ℝ, Fin 2 → ℂ) 𝓘(ℝ, ℂ) a) :=
    hap.isClosedMap _ (isClosed_criticalSet ha (by simp))
  have h0C : (0 : ℂ) ∉ a '' criticalSet 𝓘(ℝ, Fin 2 → ℂ) 𝓘(ℝ, ℂ) a := by
    rintro ⟨p, hpC, hp⟩
    obtain ⟨x, hx⟩ := mem_range_fibreEmbedding_iff.2 ⟨mem_overAffineOpen.1 p.property, hp⟩
    have h := isRegularPoint_restrictScalars_affineCoordinate x
    rw [hx] at h
    exact mem_criticalSet_iff.1 hpC (h.comp (isRegularPoint_subtype_val p))
  obtain ⟨ε, hε, hεC⟩ := Metric.isOpen_iff.1 hC.isOpen_compl 0 h0C
  -- Over the disc `ball 0 ε`, the affine coordinate is a proper submersion.
  set R : Opens ℂ := ⟨ball 0 ε, isOpen_ball⟩
  set P : Opens M := ⟨a ⁻¹' R, R.isOpen.preimage ha.continuous⟩
  set g : P → R := (R : Set ℂ).restrictPreimage a
  have hg : Manifold.IsSubmersion 𝓘(ℝ, Fin 2 → ℂ) 𝓘(ℝ, ℂ) ∞ g :=
    ((ha.restrictPreimage R).isSubmersionOfComplement_of_surjective_mfderiv (by simp)
      fun p ↦ isRegularPoint_iff.1 ((isRegularPoint_restrictPreimage_iff ha.continuous R).2
        (not_not.1 fun h ↦ hεC p.property ⟨p.val, mem_criticalSet_iff.2 h, rfl⟩))).isSubmersion
  have hgp : IsProperMap g := hap.restrictPreimage _
  have := 𝓘(ℝ, Fin 2 → ℂ).secondCountableTopology_of_sigmaCompact rationalEllipticSurface
  have := ChartedSpace.locallyCompactSpace (Fin 2 → ℂ) P
  -- The Fermat cubic is the fibre of `g` over `0`.
  set b₀ : R := ⟨0, mem_ball_self hε⟩
  set q : SmoothProjectiveHypersurface.fermat 1 3 → MapFiber g b₀ := fun x ↦
    ⟨⟨⟨fibreEmbedding x, mem_overAffineOpen.2 (snd_fibreEmbedding_mem_affineOpen x)⟩,
      Opens.mem_mk.2 (by
        simp only [a, mem_preimage, Function.comp_apply, affineCoordinate_fibreEmbedding]
        exact b₀.property)⟩,
      Subtype.ext (affineCoordinate_fibreEmbedding x)⟩
  have hqc : Continuous q :=
    ((fibreEmbedding.isEmbedding.continuous.subtype_mk _).subtype_mk _).subtype_mk _
  have hqb : Function.Bijective q := by
    refine ⟨fun x y h ↦ fibreEmbedding.isEmbedding.injective
      (congrArg (fun z : MapFiber g b₀ ↦ z.val.val.val) h), fun z ↦ ?_⟩
    obtain ⟨x, hx⟩ := mem_range_fibreEmbedding_iff.2
      ⟨mem_overAffineOpen.1 z.val.val.property, congrArg Subtype.val z.property⟩
    exact ⟨x, Subtype.ext (Subtype.ext (Subtype.ext hx))⟩
  set κ : SmoothProjectiveHypersurface.fermat 1 3 ≃ₜ MapFiber g b₀ :=
    (show Continuous (Equiv.ofBijective q hqb) from hqc).homeoOfEquivCompactToT2
  -- A trivialization of `g` around `0`, and a disc `ball 0 δ` inside its base set.
  obtain ⟨e, hb₀e, -, -⟩ :=
    hg.exists_trivialization_of_isProperMap hgp ⟨(q x₀).val, (q x₀).property⟩
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
  have hjt (p) : j p ∈ e.target := e.mem_target.2 (hιe p.2)
  -- The inverse of the trivialization over the small disc.
  have hs : Topology.IsOpenEmbedding (e.toOpenPartialHomeomorph.symm ∘ j) :=
    e.toOpenPartialHomeomorph.symm.isOpenEmbedding_comp hj (range_subset_iff.2 hjt)
  refine ⟨δ, hδ, fun p ↦ (e.toOpenPartialHomeomorph.symm (j p)).val.val,
    M.isOpen.isOpenEmbedding_subtypeVal.comp (P.isOpen.isOpenEmbedding_subtypeVal.comp hs),
    fun x ↦ ?_, fun p ↦ ⟨congrArg Subtype.val (e.proj_symm_apply' (hιe p.2)),
      mem_overAffineOpen.1 (e.toOpenPartialHomeomorph.symm (j p)).val.property⟩⟩
  have h := congrArg Subtype.val ((e.mapFiberHomeomorph hb₀e).symm_apply_apply (κ x))
  rw [Bundle.Trivialization.mapFiberHomeomorph_symm_apply] at h
  exact congrArg (fun z : P ↦ z.val.val) h

end SymplecticGeometry.rationalEllipticSurface

end
