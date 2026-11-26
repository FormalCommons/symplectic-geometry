/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Model
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import SymplecticGeometry.Topology.ComplexProjectiveSpace.SimplyConnected
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# Topology of the neighbourhoods of the exceptional divisor

For `E = ℂⁿ⁺¹` and `0 < r`, this file shows that the neighbourhood `BlowupModel.openNbhd n r` of
the exceptional divisor in the model blowup of `E` at `0` (the points whose blowdown has Euclidean
norm less than `r`) is simply connected, and that it stays path connected once the divisor is
removed.

## Main results

* `SymplecticGeometry.BlowupModel.isSimplyConnected_exceptionalDivisor`: the exceptional divisor
  is simply connected, since the zero section is an embedding of the simply connected space
  `ℙ ℂ E` onto it (`Projectivization.instSimplyConnectedSpaceComplex`).
* `SymplecticGeometry.BlowupModel.isSimplyConnected_openNbhd`: `openNbhd n r` is simply connected.
  The fibrewise scaling `(ℓ, z) ↦ (ℓ, (1 - t) z)`, `t ∈ [0, 1]`, deforms it within itself onto the
  divisor, so the inclusion of the divisor is a homotopy equivalence
  (Tau Ceti's `ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction`).
* `SymplecticGeometry.BlowupModel.isPathConnected_openNbhd_sdiff_exceptionalDivisor`: the
  complement of the divisor in `openNbhd n r` is path connected, as the image under the inverse
  of the blowdown (`blowdownDiffeomorph`) of a punctured ball of real dimension `2 (n + 1)`
  (Tau Ceti's `TauCeti.isPathConnected_ball_sdiff_singleton`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1.
-/

public section

open Set TopologicalSpace
open scoped unitInterval LinearAlgebra.Projectivization

namespace SymplecticGeometry

namespace BlowupModel

variable {n : ℕ}

variable (n) in
/-- The exceptional divisor of the model blowup is simply connected: the zero section embeds the
simply connected space `ℙ ℂ (Fin (n + 1) → ℂ)` onto it. -/
theorem isSimplyConnected_exceptionalDivisor : IsSimplyConnected (exceptionalDivisor n) := by
  have he : Topology.IsEmbedding (zeroSection : ℙ ℂ (Fin (n + 1) → ℂ) → BlowupModel n) :=
    Function.LeftInverse.isEmbedding (f := pr) pr_zeroSection continuous_pr
      continuous_zeroSection
  rw [exceptionalDivisor_eq_range]
  exact he.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace

/-- For `0 < r`, the neighbourhood `openNbhd n r` of the exceptional divisor is simply connected:
the scaling `(ℓ, z) ↦ (ℓ, (1 - t) z)` deformation retracts it onto the divisor. -/
theorem isSimplyConnected_openNbhd {r : ℝ} (hr : 0 < r) : IsSimplyConnected (openNbhd n r) := by
  -- The scaling deformation of `openNbhd n r`: at time `t`, multiply the vector by `1 - t`.
  let H : I × openNbhd n r → BlowupModel n := fun p ↦
    ⟨((p.2 : BlowupModel n).pr, (σ p.1 : ℝ) • (p.2 : BlowupModel n).blowdown),
      mem_blowupModel_iff.2 <| (p.2 : BlowupModel n).pr.submodule.smul_of_tower_mem _
        (p.2 : BlowupModel n).blowdown_mem_submodule⟩
  have hH : Continuous H := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · exact continuous_pr.comp (continuous_subtypeVal.comp continuous_snd)
    · exact (continuous_subtypeVal.comp (unitInterval.continuous_symm.comp continuous_fst)).smul
        (continuous_blowdown.comp (continuous_subtypeVal.comp continuous_snd))
  have hHB : ∀ p, H p ∈ openNbhd n r := fun p ↦ by
    have hp := mem_openNbhd_iff.1 p.2.property
    rw [mem_openNbhd_iff, blowdown_mk, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (unitInterval.nonneg _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (unitInterval.le_one _)).trans_lt hp
  refine (ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction
    (exceptionalDivisor_subset_openNbhd hr) H hH hHB (fun x ↦ ext (by simp [H]) (by simp [H]))
    ?_ ?_
    ).simplyConnectedSpace_iff.1 (isSimplyConnected_exceptionalDivisor n)
  · exact fun x ↦ mem_exceptionalDivisor_iff.2 (by simp [H])
  · intro t x hx
    rw [mem_exceptionalDivisor_iff] at hx ⊢
    simp [H, hx]

/-- For `0 < r`, the neighbourhood `openNbhd n r` with the exceptional divisor removed is path
connected: the blowdown maps it homeomorphically onto a punctured ball of `ℂⁿ⁺¹`. -/
theorem isPathConnected_openNbhd_sdiff_exceptionalDivisor {r : ℝ} (hr : 0 < r) :
    IsPathConnected (openNbhd n r \ exceptionalDivisor n) := by
  let e := TauCeti.complexToRealEuclidean (Fin (n + 1))
  let N : Opens (Fin (n + 1) → ℂ) := ⟨{z | z ≠ 0}, isOpen_ne⟩
  -- The inverse of the blowdown, `z ↦ (mk z, z)` on nonzero vectors.
  let f : N → BlowupModel n := fun z ↦ ((blowdownDiffeomorph n).symm z : BlowupModel n)
  have hf : Continuous f := continuous_subtypeVal.comp (blowdownDiffeomorph n).symm.continuous
  -- The punctured ball, in the nonzero vectors.
  let T : Set N := (fun z : N ↦ e z) ⁻¹' (Metric.ball 0 r \ {0})
  have hT : IsPathConnected T := by
    rw [Topology.IsInducing.subtypeVal.isPathConnected_iff]
    have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1) ⊕ Fin (n + 1))) := by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_sum, Fintype.card_fin]
      exact_mod_cast (by omega : 1 < n + 1 + (n + 1))
    have h := (TauCeti.isPathConnected_ball_sdiff_singleton hrank 0 hr).image
      e.symm.continuous
    convert h using 1
    ext z
    simp only [mem_image, mem_preimage, mem_sdiff, mem_singleton_iff, T, Subtype.exists]
    constructor
    · rintro ⟨z, -, h, rfl⟩
      exact ⟨e z, h, e.symm_apply_apply z⟩
    · rintro ⟨w, hw, rfl⟩
      refine ⟨e.symm w, fun h ↦ hw.2 ?_, by simpa using hw, rfl⟩
      simpa using congrArg e h
  convert hT.image hf using 1
  ext p
  simp only [mem_sdiff, mem_openNbhd_iff, mem_exceptionalDivisor_iff, mem_image]
  constructor
  · rintro ⟨hp, hp0⟩
    refine ⟨⟨p.blowdown, hp0⟩, ?_, eq_of_blowdown_eq (by simpa [f] using hp0) (by simp [f])⟩
    simp only [T, mem_preimage, mem_sdiff, Metric.mem_ball, dist_zero_right, mem_singleton_iff,
      map_eq_zero_iff e e.injective]
    exact ⟨hp, hp0⟩
  · rintro ⟨z, hz, rfl⟩
    simp only [T, mem_preimage, mem_sdiff, Metric.mem_ball, dist_zero_right,
      mem_singleton_iff] at hz
    simpa [f] using ⟨hz.1, z.property⟩

end BlowupModel

end SymplecticGeometry

end
