/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Algebra.Module.Cardinality
public import TauCeti.Topology.Algebra.Projectivization

/-!
# Complements of countable sets in projective space

Over a normed `ℝ`-algebra `𝕜` such that `Fin n → 𝕜` has real dimension greater than one, the
complement of a countable subset of the projective space `ℙ 𝕜 (Fin (n + 1) → 𝕜)` is
path-connected. In particular this holds for finite subsets of `ℂℙⁿ`, `n ≥ 1`, such as the
critical values of a Lefschetz fibration over `ℂℙ¹`.

The proof covers projective space by Tau Ceti's standard affine opens
`Projectivization.affineOpen i`, each the image of `Fin n → 𝕜` under the inverse of
`Projectivization.affineChart i`. Each affine open minus the countable set is then the image of
the complement of a countable set in `Fin n → 𝕜`, which is path-connected by Mathlib's
`Set.Countable.isPathConnected_compl_of_one_lt_rank`; and all of them contain a common point,
since the affine opens meet in a nonempty open set and a countable set has dense complement
(`Set.Countable.dense_compl`).

## Main results

* `Projectivization.affineOpen_sdiff_eq_image`: an affine open minus a set `s` is the image of the
  complement of the preimage of `s` under the inverse affine chart.
* `Projectivization.isPathConnected_compl_of_countable`,
  `Projectivization.isConnected_compl_of_countable`: the complement of a countable set is
  path-connected, hence connected.
-/

public section

open Set
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- The affine open `affineOpen i` minus a set `s` is the image, under the inverse of the affine
chart `affineChart i`, of the complement of the preimage of `s`. -/
theorem affineOpen_sdiff_eq_image (i : Fin (n + 1)) (s : Set (ℙ 𝕜 (Fin (n + 1) → 𝕜))) :
    affineOpen i \ s = (affineChart i).symm '' ((affineChart i).symm ⁻¹' s)ᶜ := by
  rw [image_compl_preimage, ← image_univ, ← affineChart_target (K := 𝕜) i,
    (affineChart i).symm_image_target_eq_source, affineChart_source]

variable [NormedAlgebra ℝ 𝕜]

/-- **The complement of a countable set in projective space is path-connected**, when the affine
space `Fin n → 𝕜` has real dimension greater than one; for instance in `ℂℙⁿ` with `n ≥ 1`. -/
theorem isPathConnected_compl_of_countable (h : 1 < Module.rank ℝ (Fin n → 𝕜))
    {s : Set (ℙ 𝕜 (Fin (n + 1) → 𝕜))} (hs : s.Countable) : IsPathConnected sᶜ := by
  have hcount (i : Fin (n + 1)) : ((affineChart (K := 𝕜) i).symm ⁻¹' s).Countable :=
    hs.preimage (Function.LeftInverse.injective fun z ↦ (affineChart i).right_inv (by simp))
  have hU (i : Fin (n + 1)) : IsPathConnected (affineOpen (K := 𝕜) i \ s) := by
    rw [affineOpen_sdiff_eq_image]
    exact ((hcount i).isPathConnected_compl_of_one_lt_rank h).image
      (continuous_affineChart_symm i)
  have hunion : sᶜ = ⋃ i, (affineOpen (K := 𝕜) i \ s) := by
    rw [← iUnion_sdiff, iUnion_affineOpen, compl_eq_univ_sdiff]
  -- A point outside `s` in every affine open: read in the affine chart of `0`, the affine opens
  -- meet in a nonempty open set, which the countable preimage of `s` cannot contain.
  have : Nontrivial (Fin n → 𝕜) := rank_pos_iff_nontrivial.1 (zero_lt_one.trans h)
  have hW : IsOpen ((affineChart (K := 𝕜) 0).symm ⁻¹' ⋂ i, affineOpen i : Set (Fin n → 𝕜)) :=
    (isOpen_iInter_of_finite fun i ↦ isOpen_affineOpen i).preimage (continuous_affineChart_symm 0)
  have hW' : ((affineChart (K := 𝕜) 0).symm ⁻¹' ⋂ i, affineOpen i : Set (Fin n → 𝕜)).Nonempty := by
    refine ⟨fun _ ↦ 1, mem_iInter.2 fun i ↦ ?_⟩
    rw [affineChart_symm_apply, mk_mem_affineOpen_iff]
    cases i using Fin.cases <;> simp
  obtain ⟨z, hzW, hzs⟩ := ((hcount 0).dense_compl ℝ).inter_open_nonempty _ hW hW'
  have hx (i : Fin (n + 1)) : (affineChart (K := 𝕜) 0).symm z ∈ affineOpen i \ s :=
    ⟨mem_iInter.1 hzW i, hzs⟩
  rw [hunion]
  refine ⟨_, mem_iUnion.2 ⟨0, hx 0⟩, fun y hy ↦ ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.1 hy
  exact ((hU i).joinedIn _ (hx i) y hi).mono (subset_iUnion (fun i ↦ affineOpen i \ s) i)

/-- **The complement of a countable set in projective space is connected**, when the affine space
`Fin n → 𝕜` has real dimension greater than one; for instance in `ℂℙⁿ` with `n ≥ 1`. -/
theorem isConnected_compl_of_countable (h : 1 < Module.rank ℝ (Fin n → 𝕜))
    {s : Set (ℙ 𝕜 (Fin (n + 1) → 𝕜))} (hs : s.Countable) : IsConnected sᶜ :=
  (isPathConnected_compl_of_countable h hs).isConnected

end Projectivization

end
