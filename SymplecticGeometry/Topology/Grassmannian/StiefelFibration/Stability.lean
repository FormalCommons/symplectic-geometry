/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Algebra.OrthogonalGroup
public import TauCeti.Topology.Algebra.UnitaryGroup
public import TauCeti.Topology.Grassmannian.StiefelFibration.ForgetLast
public import TauCeti.Topology.Grassmannian.StiefelFibration.Unitary
public import TauCeti.Topology.Homotopy.SerreFibration.Connected

/-!
# The stable range of the unitary groups

For any `RCLike 𝕜` (so `𝕜 = ℝ` or `ℂ`), write `d = dim_ℝ 𝕜`. The block embedding
`U(m, 𝕜) → U(1 + m, 𝕜)`, `B ↦ diag(1, B)`, is the inclusion of the fibre over the first standard
basis vector of the Serre fibration `U(1 + m, 𝕜) → S(𝕜^(1 + m))` that takes a unitary matrix to
its first column (`TauCeti.unitaryFrameMap` with `r = 1`, and
`TauCeti.unitaryFrameFiberHomeomorph`). The base is a real sphere of dimension `d * (m + 1) - 1`,
so its homotopy groups vanish up to degree `d * (m + 1) - 2`
(`TauCeti.finiteOrthonormalFrame.subsingleton_homotopyGroup` for `r = 1`). The inclusion of the
fibre is then `(d * (m + 1) - 2)`-connected
(`TauCeti.TopCat.isNConnected_fiberι_of_mem_serreFibrations`). Over `ℂ` this says that
`U(m) → U(m + 1)` is `2m`-connected; over `ℝ` it is the stable range of `O(m) → O(m + 1)`.

The proof follows Tau Ceti's special orthogonal analogue
`TauCeti.Matrix.SpecialOrthogonalGroup.isNConnected_fromBlocksOne`.

The hypothesis `2 ≤ d * (m + 1)` cannot be dropped: for `𝕜 = ℝ` and `m = 0` the bound truncates
to `0` in `ℕ`, and the embedding `O(0) → O(1) = {±1}` misses the path component of `-1`
(`Matrix.UnitaryGroup.not_isNConnected_fromBlocksOne_real_zero`).

## Main results

* `Matrix.UnitaryGroup.isNConnected_fromBlocksOne`: if `2 ≤ d * (m + 1)`, the block embedding
  `U(m, 𝕜) → U(1 + m, 𝕜)` is `(d * (m + 1) - 2)`-connected.
* `Matrix.UnitaryGroup.not_isNConnected_fromBlocksOne_real_zero`: the hypothesis is needed.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  §2.2 (the fibrations of unitary groups over spheres).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2
  (the fibrations `U(n - 1) → U(n) → S^(2n-1)` and the stable range of `U(n)`).
-/

public section

open TauCeti

namespace Matrix.UnitaryGroup

variable (𝕜 : Type*) [RCLike 𝕜] (m : ℕ)

/-- **Stability of the unitary groups.** For any `RCLike 𝕜`, if `2 ≤ dim_ℝ 𝕜 * (m + 1)`, the block
embedding `U(m, 𝕜) → U(1 + m, 𝕜)`, `B ↦ diag(1, B)`, is a `(dim_ℝ 𝕜 * (m + 1) - 2)`-connected
map: it induces isomorphisms on `π_k` for `k < dim_ℝ 𝕜 * (m + 1) - 2` and surjections for
`k = dim_ℝ 𝕜 * (m + 1) - 2`. Over `ℂ` the bound is `2m`. -/
theorem isNConnected_fromBlocksOne (h : 2 ≤ Module.finrank ℝ 𝕜 * (m + 1)) :
    (⟨fromBlocksOne 𝕜 1 m, continuous_fromBlocksOne m⟩ :
      C(unitaryGroup (Fin m) 𝕜, unitaryGroup (Fin (1 + m)) 𝕜)).IsNConnected
        (Module.finrank ℝ 𝕜 * (m + 1) - 2) := by
  let p : _root_.TopCat.of (unitaryGroup (Fin (1 + m)) 𝕜) ⟶
      _root_.TopCat.of (finiteOrthonormalFrame 𝕜 1 (1 + m)) :=
    _root_.TopCat.ofHom ⟨unitaryFrameMap 1 m, continuous_unitaryFrameMap 𝕜 1 m⟩
  -- The base, the unit sphere of `𝕜^(1 + m)`, is `(dim_ℝ 𝕜 * (m + 1) - 2)`-connected, so the
  -- fibre over the first standard basis vector is as connected in the total space.
  have hfib : (p.fiberι (unitaryFrameMap 1 m 1)).hom.IsNConnected
      (Module.finrank ℝ 𝕜 * (m + 1) - 2) :=
    TopCat.isNConnected_fiberι_of_mem_serreFibrations unitaryFrameMap_mem_serreFibrations
      fun k hk ↦ finiteOrthonormalFrame.subsingleton_homotopyGroup
        (by rw [Nat.card_fin, mul_one, add_comm 1 m, mul_add _ (m + 1)]; omega) _
  -- The block embedding is the fibre inclusion after the homeomorphism of `U(m)` with the fibre.
  let φ := unitaryFrameFiberHomeomorph 𝕜 1 m
  convert hfib.comp (φ.toHomotopyEquiv.isWeakHomotopyEquivalence.isNConnected _) using 1
  ext B : 1
  exact (coe_unitaryFrameFiberHomeomorph_apply B).symm.trans
    (TopCat.Hom.fiberι_apply p _ (φ B)).symm

/-- **The hypothesis of `isNConnected_fromBlocksOne` is needed.** For `𝕜 = ℝ` and `m = 0` the
bound `dim_ℝ ℝ * (0 + 1) - 2` truncates to `0`, but the block embedding `O(0) → O(1)` is not
`0`-connected: its image is `{1}`, and `-1 ∈ O(1)` is not joined to `1` by a path, since the
entry of a `1 × 1` orthogonal matrix is `±1` and never `0`. -/
theorem not_isNConnected_fromBlocksOne_real_zero :
    ¬ (⟨fromBlocksOne ℝ 1 0, continuous_fromBlocksOne 0⟩ :
      C(unitaryGroup (Fin 0) ℝ, unitaryGroup (Fin (1 + 0)) ℝ)).IsNConnected
        (Module.finrank ℝ ℝ * (0 + 1) - 2) := fun h ↦ by
  obtain ⟨B, hB⟩ := h.exists_joined (-1)
  have := Matrix.joined_orthogonalGroup_iff_det_eq.1 hB
  simp [Subsingleton.elim B 1, Matrix.det_unique, Unitary.coe_neg] at this
  norm_num at this

end Matrix.UnitaryGroup

end
