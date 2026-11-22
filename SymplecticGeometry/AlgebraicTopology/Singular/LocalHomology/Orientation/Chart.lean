/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Chart

/-!
# Radial projection commutes with linear isometries

A linear isometry equivalence `e : E ≃ₗᵢ[ℝ] F` followed by radial projection about `e p` onto the
unit sphere of `F` is radial projection about `p` onto the unit sphere of `E` followed by the
restriction of `e` to the unit spheres
(`LinearIsometryEquiv.snd_ofSubsetMap_comp_complSingletonHomotopyEquivSphere`).

This file is a part of Tau Ceti's
`TauCeti/AlgebraicTopology/Singular/LocalHomology/Orientation/Chart.lean`, as of the commit
`55525ca744` (TauCetiProject/TauCeti#37381) of Tau Ceti's main branch, not yet in the pinned
release. That commit made the lemma public and general, from a private lemma about the point
`e p`; it is stated here under its Tau Ceti name, so that moving Tau Ceti past it deletes this
file without renames. The statement and the proof are Tau Ceti's, unchanged.

The local generators of Tau Ceti's file are those of an oriented coordinate chart in Hatcher's
*Algebraic Topology*, Section 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module

universe w

namespace TauCeti

section LinearIsometryEquiv

variable {E F : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Applying a linear isometry equivalence followed by radial projection about `e p` is radial
projection about `p` followed by the restriction of `e` to the unit spheres. -/
theorem
    _root_.LinearIsometryEquiv.snd_ofSubsetMap_comp_complSingletonHomotopyEquivSphere
    (e : E ≃ₗᵢ[ℝ] F) (p : E) (q : F) (hq : e p = q) :
    TopPair.Hom.snd (TopPair.ofSubsetMap (X := TopCat.of E) (Y := TopCat.of F)
        (TopCat.ofHom ⟨e, e.continuous⟩) (B := {p}ᶜ) (B' := {q}ᶜ)
        (fun _ hy h ↦ hy (e.injective (h.trans hq.symm)))) ≫
      TopCat.ofHom (complSingletonHomotopyEquivSphere q).toFun =
    TopCat.ofHom (complSingletonHomotopyEquivSphere p).toFun ≫
      TopCat.ofHom ⟨e.toLinearIsometry.unitSphereMap,
        e.toLinearIsometry.continuous_unitSphereMap⟩ := by
  subst q
  ext z
  -- The subspace of `TopPair.ofSubset` is the subtype only after unfolding the pair.
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  refine (coe_complSingletonHomotopyEquivSphere_apply (e p) _).trans ?_
  -- Unfold `TopPair.ofSubset` on the subspace component to apply `TopPair.ofSubsetMap_snd_apply`.
  erw [TopPair.ofSubsetMap_snd_apply]
  simp only [TopCat.hom_ofHom, ContinuousMap.coe_mk, LinearIsometry.coe_unitSphereMap_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, ← map_sub, e.norm_map, ← map_smul]
  exact (congrArg e (coe_complSingletonHomotopyEquivSphere_apply p z)).symm

end LinearIsometryEquiv

end TauCeti
