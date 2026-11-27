/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.Splitting
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.DoubleClutching
import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Flow.Basic
import SymplecticGeometry.Topology.Homotopy.Extension.Collar
import SymplecticGeometry.Geometry.Manifold.Instances.SymplecticGroup.SmoothApprox
import SymplecticGeometry.Geometry.Manifold.Boundary.Charts

/-!
# Extending maps from the boundary of a surface into the symplectic group

Let `S` be a compact connected surface with boundary, modelled on the half-plane, and `o` an
orientation of its interior. A continuous map `Ψ : ∂S → Sp(2n)` extends to a continuous map
`S → Sp(2n)` exactly when its boundary Maslov index `o.boundaryMaslovIndex Ψ`, the degree of
`ρ ∘ Ψ` on the boundary for the Maslov phase `ρ`, vanishes
(`TauCeti.Manifold.Orientation.exists_extension_iff_boundaryMaslovIndex_eq_zero`). This is the
lemma behind the description of the first Chern number through a splitting of a closed surface
(`Splitting.lean`).

A map that extends has index `0` (`boundaryMaslovIndex_eq_zero_of_extend`). For the converse we
may assume that `∂S` is not empty, and reindex the matrices by `Fin k`. By Whitney approximation
(`ContinuousMap.exists_homotopic_contMDiff_symplecticGroup`), `Ψ` is homotopic to a smooth map
`Ψ'`, which has index `0` too. Choose a smooth collar `c` of `∂S`. The bundle over the closed
double of `S` clutched by `Ψ'` (`SymplecticSurfaceBundle.doubleClutching`) has first Chern number
the index of `Ψ'` (`symplecticChernNumber_doubleClutching`), so it is trivial
(`symplecticChernNumber_eq_zero_iff`), and has a global symplectic frame `Θ`. Read in the frames
of its two charts along the two copies of `S`, `Θ` gives continuous maps `A` and `B` from `S` to
the symplectic group; on `∂S`, where the copies meet and the frames differ by `Ψ'`, these satisfy
`A = Ψ' B`, so `A B⁻¹` extends `Ψ'`. Last, `∂S` is collared, so it has the homotopy extension
property (`TauCeti.IsCollared.hasHomotopyExtensionProperty_range`), and the homotopy from `Ψ'` to
`Ψ` extends to one from `A B⁻¹` to an extension of `Ψ`.

The book glues discs into the boundary circles of `S` instead. The double avoids parametrizing
`∂S` by circles and comparing their orientations with the boundary class.

## Main results

* `TauCeti.Manifold.Orientation.exists_extension_iff_boundaryMaslovIndex_eq_zero`: a map from the
  boundary of a compact connected surface to the symplectic group extends over the surface if
  and only if its boundary Maslov index is `0`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], Lemma 2.7.3
  (the extension criterion).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218, 2013, Theorem 6.26
  (Whitney approximation).
-/

public section

noncomputable section

open Set Function Topology Manifold TauCeti TauCeti.GLSymplectic SymplecticGeometry
open scoped Manifold ContDiff

/-! ### The extension lemma -/

namespace TauCeti.Manifold.Orientation

open SmoothCollar.Double SymplecticGeometry.Bundle SymplecticGeometry.Bundle.SymplecticSurfaceBundle
open scoped Matrix.Norms.Operator

variable {S : Type} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S] [T2Space S] [CompactSpace S] [ConnectedSpace S]
  (o : Manifold.Orientation (𝓡 2) ((𝓡∂ 2).interior S) (Fin 2))

/-- The extension lemma for a smooth map `Ψ` from a nonempty boundary: the bundle over the double
of `S` clutched by `Ψ` is trivial, and a global frame of it gives the extension. -/
private theorem exists_extension_of_contMDiff {κ : Type} [Fintype κ] [DecidableEq κ]
    (hS : ((𝓡∂ 2).boundary S).Nonempty) (Ψ : C((𝓡∂ 2).boundary S, GLSymplectic κ ℝ))
    (hΨ : letI := Matrix.linftyOpTopologicalSpace (κ ⊕ κ) (κ ⊕ κ) ℝ
      ContMDiff (𝓡 1) 𝓘(ℝ, Lie.SymplecticGroupModel κ ℝ) ∞
        fun x ↦ (symplecticGroupContinuousMulEquiv κ ℝ).symm (Ψ x))
    (h : o.boundaryMaslovIndex Ψ = 0) :
    ∃ Φ : C(S, GLSymplectic κ ℝ), ∀ z : (𝓡∂ 2).boundary S, Φ z = Ψ z := by
  have := hS.to_subtype
  obtain ⟨c⟩ : Nonempty (SmoothCollar 1 ∞ S) := inferInstance
  -- The clutched bundle has number `0`, so it is trivial, with a global symplectic frame.
  obtain ⟨Φ⟩ := symplecticChernNumber_eq_zero_iff.1
    ((symplecticChernNumber_doubleClutching c o hS Ψ hΨ).trans h)
  let eκ : κ ≃ Fin (doubleClutching c o hS Ψ hΨ).n :=
    (Fintype.equivFin κ).trans (finCongr (doubleClutching_n c o hS Ψ hΨ).symm)
  have hΘ := Φ.isSymplecticFrameOn_trans_symm_toFun
    (e := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (eκ.sumCongr eκ)).toContinuousLinearEquiv)
    (isSymplectomorphism_piLpCongrLeft_sumCongr _)
  -- Read it in the frames of the two charts, along the two copies of `S`. The frames are given
  -- first, so that the base of the bundle is the bundled double.
  have hA := ContMDiffTwoForm.IsSymplecticFrameOn.exists_frameTransition
    (M := ClosedConnectedOrientedSurface.double c o hS) (I := 𝓡 2) (X := S)
    (h := isSymplecticFrameOn_doubleClutchingFrame_true c o hS Ψ hΨ) (h' := hΘ)
  obtain ⟨A, hA⟩ := hA (isOpen_range_inlInterior_union_bandMap_image c) isOpen_univ
    ⟨inl c, (inl c).continuous⟩ fun x ↦
      ⟨preimage_height_Iic_subset_range_inlInterior_union_bandMap_image c (height_inl_nonpos c x),
        mem_univ _⟩
  have hB := ContMDiffTwoForm.IsSymplecticFrameOn.exists_frameTransition
    (M := ClosedConnectedOrientedSurface.double c o hS) (I := 𝓡 2) (X := S)
    (h := isSymplecticFrameOn_doubleClutchingFrame_false c o hS Ψ hΨ) (h' := hΘ)
  obtain ⟨B, hB⟩ := hB (isOpen_range_inrInterior_union_bandMap_image c) isOpen_univ
    ⟨inr c, (inr c).continuous⟩ fun x ↦
      ⟨preimage_height_Ici_subset_range_inrInterior_union_bandMap_image c (height_inr_nonneg c x),
        mem_univ _⟩
  refine ⟨A * B⁻¹, fun z ↦ ?_⟩
  -- On `∂S` the two copies agree, and there `A = Ψ * B`.
  have hAB : A z = Ψ z * B z := by
    have hw : inl c z = inr c z := inl_coe_eq_inr c z
    have hz : bandProj c (inr c z) = z := by
      rw [← hw, ← bandMap_zero, bandProj_bandMap c (by norm_num)]
    refine Subtype.ext (Units.ext (Matrix.toEuclideanLin.injective (LinearMap.ext fun v ↦ ?_)))
    have h₁ := (hA z v).symm
    rw [show (⟨inl c, (inl c).continuous⟩ : C(S, ClosedConnectedOrientedSurface.double c o hS)) z =
      (⟨inr c, (inr c).continuous⟩ : C(S, ClosedConnectedOrientedSurface.double c o hS)) z
      from hw] at h₁
    have h₃ := doubleClutchingFrame_false_apply c o hS Ψ hΨ (inr c z)
      (Matrix.toEuclideanLin (B z : GL (κ ⊕ κ) ℝ) v)
    rw [hz] at h₃
    have hm : Matrix.toEuclideanLin (((Ψ z * B z : GLSymplectic κ ℝ) : GL (κ ⊕ κ) ℝ) :
          Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) v =
        Matrix.toEuclideanLin ((Ψ z : GL (κ ⊕ κ) ℝ) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ)
          (Matrix.toEuclideanLin ((B z : GL (κ ⊕ κ) ℝ) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) v) := by
      simp
    rw [hm]
    exact (doubleClutchingFrame c o hS Ψ hΨ true _).injective ((h₁.trans (hB z v)).trans h₃)
  rw [ContinuousMap.mul_apply, ContinuousMap.inv_apply, hAB, mul_inv_cancel_right]

local instance : IsManifold (𝓡 1) ∞ ((𝓡∂ 2).boundary S) := isManifold_boundary S

/-- **The extension lemma.** Let `S` be a compact connected surface with boundary, modelled on the
half-plane, and `o` an orientation of its interior. A continuous map `Ψ : ∂S → Sp(2n)` is the
restriction of a continuous map `S → Sp(2n)` if and only if its boundary Maslov index for `o` is
`0`.

The boundary may be empty, and then both sides hold. Connectedness is needed: on two discs, a map
of Maslov index `1` on one boundary circle and `-1` on the other has index `0` but extends over
neither disc.

Milestone: *First Chern number of symplectic vector bundles over surfaces*. -/
theorem exists_extension_iff_boundaryMaslovIndex_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    (Ψ : C((𝓡∂ 2).boundary S, GLSymplectic n ℝ)) :
    (∃ Φ : C(S, GLSymplectic n ℝ), ∀ z : (𝓡∂ 2).boundary S, Φ z = Ψ z) ↔
      o.boundaryMaslovIndex Ψ = 0 := by
  refine ⟨fun ⟨Φ, hΦ⟩ ↦ o.boundaryMaslovIndex_eq_zero_of_extend Φ hΦ, fun h ↦ ?_⟩
  rcases ((𝓡∂ 2).boundary S).eq_empty_or_nonempty with hS | hS
  · exact ⟨1, fun z ↦ absurd z.property (eq_empty_iff_forall_notMem.1 hS _)⟩
  -- Reindex the matrices by `Fin (card n)`, and make the map smooth.
  let e := Fintype.equivFin n
  let r : C(GLSymplectic n ℝ, GLSymplectic (Fin (Fintype.card n)) ℝ) :=
    reindexContinuousMulEquiv ℝ e
  obtain ⟨Ψ', ⟨F⟩, hΨ'⟩ := (r.comp Ψ).exists_homotopic_contMDiff_symplecticGroup (I := 𝓡 1)
  have h' : o.boundaryMaslovIndex Ψ' = 0 := by
    rw [← o.boundaryMaslovIndex_eq_of_homotopy F, boundaryMaslovIndex_reindex, h]
  obtain ⟨Φ', hΦ'⟩ := exists_extension_of_contMDiff o hS Ψ' hΨ' h'
  -- The collared boundary has the homotopy extension property, which turns the extension `Φ'` of
  -- `Ψ'` into an extension of `r ∘ Ψ`.
  have hHEP : HasHomotopyExtensionProperty ((𝓡∂ 2).boundary S) := by
    have h : HasHomotopyExtensionProperty (range ((↑) : (𝓡∂ 2).boundary S → S)) :=
      (isCollared_subtypeVal_boundary_of_compactSpace (n := 1)).hasHomotopyExtensionProperty_range
    rwa [Subtype.range_coe] at h
  obtain ⟨Φ'', G, hG⟩ := hHEP.exists_homotopy_of_restrict
    ((𝓡∂ 2).isClosed_boundary_of_finiteDimensional S) Φ'
    (F.symm.cast (ContinuousMap.ext hΦ').symm rfl)
  refine ⟨((reindexContinuousMulEquiv ℝ e).symm : C(_, _)).comp Φ'', fun z ↦ ?_⟩
  have h₁ : Φ'' z = r (Ψ z) := by
    rw [← G.apply_one, hG 1 z]
    simp
  rw [ContinuousMap.comp_apply, h₁, ContinuousMap.coe_ofClass, ContinuousMap.coe_ofClass]
  exact (reindexContinuousMulEquiv ℝ e).symm_apply_apply _

end TauCeti.Manifold.Orientation

end
