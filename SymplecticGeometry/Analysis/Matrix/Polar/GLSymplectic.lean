/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Reindex
public import TauCeti.Analysis.Matrix.Polar.GLSymplectic
public import TauCeti.Analysis.Matrix.SymplecticGroup.Connected
public import TauCeti.Topology.Algebra.Matrix.Realify
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.MaximalCompact
public import TauCeti.Topology.Homotopy.DeformationRetract
import SymplecticGeometry.Analysis.Matrix.Polar.Deformation
import SymplecticGeometry.Analysis.Matrix.Polar.Symplectic
import SymplecticGeometry.Analysis.Matrix.Polar.Basic

/-!
# The unitary group is a deformation retract of the real symplectic group

Let `U(n)` be the group of orthogonal symplectic matrices of size `2n`, as the subgroup
`GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ)` of the general linear group. Tau Ceti's
symplectic polar homotopy `TauCeti.GLSymplectic.polarHomotopy` contracts the positive factor of
`Ψ = P U` and ends at the orthogonal polar factor `U`. This file shows that it fixes `U(n)` at
all times, so that it is a strong deformation retraction of `Sp(2n)` onto `U(n)`; that at time
`t` it is the map `Ψ ↦ Ψ (ΨᵀΨ) ^ (-t / 2)`; and that the inclusion `U(n) → Sp(2n)` is a
homotopy equivalence, with the orthogonal polar factor as homotopy inverse.

With Tau Ceti's powers of positive symplectic matrices (`SymplecticGroup.rpow_mem`), the right
polar decomposition of `SymplecticGeometry.Analysis.Matrix.Polar.Symplectic`, Tau Ceti's
maximality of `U(n)` among compact subgroups and its path-connectedness of `Sp(2n)`, this gives
the theorem `TauCeti.GLSymplectic.polar_maximal_isCompact_deformationRetract`.

## Main definitions

* `TauCeti.GLSymplectic.polarHomotopyRel`: the symplectic polar homotopy, as a homotopy relative
  to `U(n)`.
* `TauCeti.GLSymplectic.polarHomotopyEquiv`: the homotopy equivalence `U(n) ≃ₕ Sp(2n)` given by
  the inclusion.
* `TauCeti.GLSymplectic.ofUnitaryHomotopyEquiv`: the homotopy equivalence `U(n) ≃ₕ Sp(2n)` from
  the complex unitary group, given by the realification `TauCeti.GLSymplectic.ofUnitary`.

## Main results

* `TauCeti.GLSymplectic.polarHomotopy_apply_inclusion`: the polar homotopy fixes `U(n)`.
* `TauCeti.GLSymplectic.coe_polarHomotopy_apply_eq_mul_rpow`: at time `t` the polar homotopy is
  `Ψ ↦ Ψ (ΨᵀΨ) ^ (-t / 2)`.
* `TauCeti.GLSymplectic.polar_maximal_isCompact_deformationRetract`: the polar decomposition of
  a real symplectic matrix, maximal compactness of `U(n)`, the deformation retraction and the
  homotopy equivalence, and connectedness of `Sp(2n)`.
* `TauCeti.GLSymplectic.coe_polarUnitary_reindex`: the orthogonal polar factor commutes with
  reindexing along an equivalence of index types.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2, Lemma 2.2.3, Proposition 2.2.4 and Remark 2.2.5.
-/

public section

open Matrix Matrix.GeneralLinearGroup
open scoped MatrixOrder unitInterval ContinuousMap

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The symplectic polar homotopy fixes every orthogonal symplectic matrix at every time. -/
@[simp]
theorem polarHomotopy_apply_inclusion (t : I)
    (U : ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ))) :
    polarHomotopy (t, Subgroup.inclusion inf_le_left U) = Subgroup.inclusion inf_le_left U := by
  have hU : (U : GL (n ⊕ n) ℝ) = Unitary.toUnits ⟨_, by
      simpa [mem_unitarySubgroup_iff, Units.unitary_eq] using (Subgroup.mem_inf.1 U.property).2⟩ :=
    Units.ext rfl
  refine Subtype.ext ?_
  rw [coe_polarHomotopy_apply, Subgroup.coe_inclusion, hU, polarDeformation_toUnits]

/-- The symplectic polar homotopy, from the identity of `Sp(2n)` to the orthogonal polar factor,
as a homotopy relative to the orthogonal symplectic matrices `U(n)`: a strong deformation
retraction of `Sp(2n)` onto `U(n)`. -/
noncomputable def polarHomotopyRel :
    ContinuousMap.HomotopyRel (ContinuousMap.id (GLSymplectic n ℝ))
      ⟨fun A ↦ Subgroup.inclusion inf_le_left (polarUnitary A),
        continuous_inclusion_polarUnitary⟩
      (Set.range (Subgroup.inclusion (inf_le_left (b := unitarySubgroup (GL (n ⊕ n) ℝ))))) where
  toHomotopy := polarHomotopy
  prop' := by
    rintro t _ ⟨U, rfl⟩
    exact polarHomotopy_apply_inclusion t U

/-- The relative symplectic polar homotopy evaluates to the symplectic polar homotopy. -/
@[simp]
theorem polarHomotopyRel_apply (p : I × GLSymplectic n ℝ) :
    polarHomotopyRel p = polarHomotopy p :=
  (rfl)

/-- At time `t`, the symplectic polar homotopy is the map `Ψ ↦ Ψ (ΨᵀΨ) ^ (-t / 2)`. -/
theorem coe_polarHomotopy_apply_eq_mul_rpow (t : I) (A : GLSymplectic n ℝ) :
    (((polarHomotopy (t, A) : GLSymplectic n ℝ) : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
        (((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
          ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) ^ (-((t : ℝ) / 2)) := by
  rw [coe_polarHomotopy_apply, coe_polarDeformation_eq_mul_rpow, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial]

/-- **`U(n)` is homotopy equivalent to `Sp(2n)`.** The inclusion of the orthogonal symplectic
matrices in the real symplectic group is a homotopy equivalence, with the orthogonal polar factor
as homotopy inverse. -/
noncomputable def polarHomotopyEquiv :
    ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ)) ≃ₕ GLSymplectic n ℝ :=
  .ofDeformationRetraction ⟨_, Subgroup.continuous_inclusion inf_le_left⟩
    ⟨_, continuous_polarUnitary⟩ polarUnitary_inclusion ⟨polarHomotopy.symm⟩

/-- The homotopy equivalence `U(n) ≃ₕ Sp(2n)` is the inclusion. -/
@[simp]
theorem polarHomotopyEquiv_apply (U : ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ))) :
    polarHomotopyEquiv U = Subgroup.inclusion inf_le_left U :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_apply _ _ _ _ U

/-- The homotopy inverse of the inclusion `U(n) → Sp(2n)` is the orthogonal polar factor. -/
@[simp]
theorem polarHomotopyEquiv_symm_apply (A : GLSymplectic n ℝ) :
    polarHomotopyEquiv.symm A = polarUnitary A :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_symm_apply _ _ _ _ A

/-- The realification `ofUnitary` of complex unitary matrices of size `n` into `Sp(2n)` is a
homotopy equivalence: it is the homeomorphism of the complex unitary group with the orthogonal
symplectic matrices, followed by their inclusion in `Sp(2n)`. -/
noncomputable def ofUnitaryHomotopyEquiv : unitaryGroup n ℂ ≃ₕ GLSymplectic n ℝ :=
  unitaryGroupEquivSymplecticInfOrthogonal.toHomeomorph.toHomotopyEquiv.trans polarHomotopyEquiv

/-- The homotopy equivalence `ofUnitaryHomotopyEquiv` is the realification `ofUnitary`. -/
@[simp]
theorem ofUnitaryHomotopyEquiv_apply (U : unitaryGroup n ℂ) :
    ofUnitaryHomotopyEquiv U = ofUnitary U := by
  simp [ofUnitaryHomotopyEquiv, ofUnitary_apply]

/-- **Polar decomposition and the maximal compact subgroup of `Sp(2n)`.** For real matrices of
size `2n`:
1. a positive definite symplectic matrix `P` has every real power `P ^ α` symplectic;
2. a symplectic matrix `Ψ` is `U P` with `U` orthogonal and symplectic, that is, in `U(n)`, and
  `P` positive definite and symplectic, for exactly one pair `(U, P)`, namely
  `U = Ψ (ΨᵀΨ) ^ (-1 / 2)` and `P = (ΨᵀΨ) ^ (1 / 2)`;
3. `U(n)` is compact and no compact subgroup of `Sp(2n)` strictly contains it; the maps
  `Ψ ↦ Ψ (ΨᵀΨ) ^ (-t / 2)`, `0 ≤ t ≤ 1`, form a homotopy relative to `U(n)` from the identity
  to a retraction onto `U(n)`; the inclusion `U(n) → Sp(2n)` is a homotopy equivalence; and
  `Sp(2n)` is path-connected.

Milestone: *Symplectic polar decomposition and the maximal compact subgroup*. -/
theorem polar_maximal_isCompact_deformationRetract :
    (∀ P : Matrix (n ⊕ n) (n ⊕ n) ℝ, P.PosDef → P ∈ symplecticGroup n ℝ →
      ∀ α : ℝ, P ^ α ∈ symplecticGroup n ℝ) ∧
    (∀ Ψ ∈ symplecticGroup n ℝ, ∀ U P : Matrix (n ⊕ n) (n ⊕ n) ℝ,
      (U ∈ symplecticGroup n ℝ ∧ U ∈ orthogonalGroup (n ⊕ n) ℝ ∧ P.PosDef ∧
          P ∈ symplecticGroup n ℝ ∧ U * P = Ψ) ↔
        (U = Ψ * (Ψᵀ * Ψ) ^ (-(1 / 2 : ℝ)) ∧ P = (Ψᵀ * Ψ) ^ (1 / 2 : ℝ))) ∧
    Maximal (fun K : Subgroup (GLSymplectic n ℝ) ↦ IsCompact (K : Set (GLSymplectic n ℝ)))
      ((unitarySubgroup (GL (n ⊕ n) ℝ)).subgroupOf (GLSymplectic n ℝ)) ∧
    (∃ r : C(GLSymplectic n ℝ, ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ))),
      (∀ U, r (Subgroup.inclusion inf_le_left U) = U) ∧
      ∃ H : ContinuousMap.HomotopyRel (ContinuousMap.id (GLSymplectic n ℝ))
          ((⟨_, Subgroup.continuous_inclusion inf_le_left⟩ :
            C(↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ)), GLSymplectic n ℝ)).comp r)
          (Set.range (Subgroup.inclusion (inf_le_left (b := unitarySubgroup (GL (n ⊕ n) ℝ))))),
        ∀ (t : I) (A : GLSymplectic n ℝ),
          (((H (t, A) : GLSymplectic n ℝ) : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
            ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
              (((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
                ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) ^ (-((t : ℝ) / 2))) ∧
    (∃ e : ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ)) ≃ₕ GLSymplectic n ℝ,
      ∀ U, e U = Subgroup.inclusion inf_le_left U) ∧
    IsPathConnected (symplecticGroup n ℝ : Set (Matrix (n ⊕ n) (n ⊕ n) ℝ)) := by
  refine ⟨fun P hP hPs α ↦ SymplecticGroup.rpow_mem hP.posSemidef hPs α, fun Ψ hΨ U P ↦ ?_,
    maximal_isCompact_unitarySubgroup,
    ⟨⟨_, continuous_polarUnitary⟩, polarUnitary_inclusion, polarHomotopyRel,
      coe_polarHomotopy_apply_eq_mul_rpow⟩,
    ⟨polarHomotopyEquiv, polarHomotopyEquiv_apply⟩, isPathConnected_symplecticGroup n⟩
  rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose]
  exact SymplecticGroup.unitary_mul_posDef_eq_iff hΨ

/-- The orthogonal polar factor commutes with reindexing: the polar factor of a symplectic matrix
reindexed along `e : n ≃ κ` is the polar factor of the matrix, reindexed along `e ⊕ e`. -/
theorem coe_polarUnitary_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (e : n ≃ κ)
    (A : GLSymplectic n ℝ) :
    ((polarUnitary (GLSymplectic.reindex ℝ e A) : GL (κ ⊕ κ) ℝ) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) =
      Matrix.reindex (e.sumCongr e) (e.sumCongr e)
        ((polarUnitary A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  rw [coe_polarUnitary, coe_reindex, GeneralLinearGroup.coe_polarUnitary_reindex,
    ← coe_polarUnitary]

end TauCeti.GLSymplectic

end
