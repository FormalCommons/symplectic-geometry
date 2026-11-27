/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.PolarCompatible
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.MaximalCompact
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Unitary
public import TauCeti.Topology.Algebra.Group.Subgroup
import SymplecticGeometry.LinearAlgebra.ComplexStructure.Standard
import SymplecticGeometry.LinearAlgebra.Symplectic.Compatible
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix
import SymplecticGeometry.Topology.Algebra.Matrix.GeneralLinearGroup

/-!
# Compact subgroups of the symplectic group

This file proves that every compact subgroup `K` of the real symplectic group
`Sp(2n, ℝ) = GLSymplectic ι ℝ` is conjugate, inside `Sp(2n, ℝ)`, to a subgroup of the realified
unitary group `U(n) = Sp(2n, ℝ) ∩ O(2n)` (`TauCeti.GLSymplectic.inf_unitarySubgroup`). Together
with Tau Ceti's `TauCeti.GLSymplectic.maximal_isCompact_unitarySubgroup`, it follows that the
maximal compact subgroups of `Sp(2n, ℝ)` are exactly the conjugates of `U(n)`.

The argument: `K` acts continuously on `StdSpace ι`, through the restriction of
`Matrix.GeneralLinearGroup.contRep`, and preserves `ω₀`, so it preserves a
compatible complex structure `J`
(`TauCeti.SymplecticForm.exists_compatible_forall_isComplexLinearMap`). A symplectic matrix `P`
carries `J₀` to `J` (`SymplecticGeometry.compatible_iff_exists_isSymplectomorphism_stdForm`), so
every `P⁻¹ k P`, for `k ∈ K`, is symplectic and fixes `J₀`. It therefore lies in the realified
`GL(n, ℂ)` (`SymplecticGeometry.stabilizer_stdComplexStructure`), and so in the realified `U(n)`
(`TauCeti.GLSymplectic.inf_range_realify`).

## Main results

* `TauCeti.GLSymplectic.exists_conj_smul_le_unitarySubgroup`: every compact subgroup of
  `GLSymplectic ι ℝ` has a conjugate inside the orthogonal symplectic matrices.
* `TauCeti.GLSymplectic.maximal_isCompact_iff`: the maximal compact subgroups of
  `GLSymplectic ι ℝ` are exactly the conjugates of the orthogonal symplectic matrices.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.5.8.
-/

public section

namespace TauCeti.GLSymplectic

open SymplecticGeometry _root_.Matrix _root_.Matrix.GeneralLinearGroup
open scoped Pointwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Compact subgroups of the symplectic group.** If `K` is a compact subgroup of the real
symplectic group `GLSymplectic ι ℝ`, then a suitable symplectic matrix conjugates `K` into the
orthogonal symplectic matrices. These form the realified unitary group `U(n)`, by
`TauCeti.GLSymplectic.inf_unitarySubgroup`.

Milestone: *Compact subgroups of the symplectic group*. -/
theorem exists_conj_smul_le_unitarySubgroup {K : Subgroup (GLSymplectic ι ℝ)}
    (hK : IsCompact (K : Set (GLSymplectic ι ℝ))) :
    ∃ g : GLSymplectic ι ℝ, MulAut.conj g • K ≤
      (unitarySubgroup (GL (ι ⊕ ι) ℝ)).subgroupOf (GLSymplectic ι ℝ) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- A `K`-invariant complex structure `J` compatible with `ω₀`.
  set ρ := (contRep ℝ (ι ⊕ ι)).restrict ((GLSymplectic ι ℝ).subtype.comp K.subtype)
  have hρ : Continuous ρ := (continuous_contRep ℝ (ι ⊕ ι)).comp
    (continuous_subtypeVal.comp continuous_subtypeVal)
  obtain ⟨J, hJ, hKJ⟩ := (stdForm ι).exists_compatible_forall_isComplexLinearMap ρ hρ
    fun k u v ↦ by
      simp only [ρ, ContRepresentation.restrict_apply_apply, contRep_apply]
      exact mem_symplecticGroup_iff_forall_stdForm_toEuclideanCLM.1
        (mem_iff_mem_symplecticGroup.1 (k : GLSymplectic ι ℝ).property) u v
  have hfix (k : K) : ((k : GLSymplectic ι ℝ) : GL (ι ⊕ ι) ℝ) • J = J := by
    rw [AlmostComplexStructure.generalLinearGroup_smul_def,
      AlmostComplexStructure.transport_eq_iff_isComplexLinearMap]
    convert hKJ k using 1
    ext v : 1
    simp [ρ]
  -- A symplectic matrix `P` carrying `J₀` to `J`.
  obtain ⟨Ψ, hΨ, hΨJ⟩ := (compatible_iff_exists_isSymplectomorphism_stdForm finrank_stdSpace).1 hJ
  set P : GL (ι ⊕ ι) ℝ := ofEuclideanCLE Ψ.toContinuousLinearEquiv
  have hP : P ∈ GLSymplectic ι ℝ := by
    rw [mem_GLSymplectic_iff_isSymplectomorphism]
    simpa [P] using hΨ
  have hPJ : P • stdComplexStructure ι = J := by
    rw [AlmostComplexStructure.ofEuclideanCLE_smul,
      LinearEquiv.toLinearEquiv_toContinuousLinearEquiv,
      AlmostComplexStructure.transport_eq_iff_isComplexLinearMap]
    exact hΨJ
  refine ⟨(⟨P, hP⟩ : GLSymplectic ι ℝ)⁻¹, fun _ hx ↦ ?_⟩
  obtain ⟨k, hk, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hx
  rw [Subgroup.mem_subgroupOf]
  -- `P⁻¹ k P` is symplectic and fixes `J₀`, so it lies in the realified unitary group.
  have hmem : ((MulAut.conj (⟨P, hP⟩ : GLSymplectic ι ℝ)⁻¹ • k : GLSymplectic ι ℝ) :
      GL (ι ⊕ ι) ℝ) ∈ GLSymplectic ι ℝ ⊓ (realify ι ℂ).range := by
    refine Subgroup.mem_inf.2 ⟨Subtype.coe_prop _, ?_⟩
    rw [← stabilizer_stdComplexStructure, MulAction.mem_stabilizer_iff]
    simp only [MulAut.smul_def, MulAut.conj_apply, inv_inv, Subgroup.coe_mul,
      Subgroup.coe_inv, mul_smul, hPJ, hfix ⟨k, hk⟩]
    rw [inv_smul_eq_iff, hPJ]
  rw [inf_range_realify, ← inf_unitarySubgroup] at hmem
  exact hmem.2

/-- **Maximal compact subgroups of the symplectic group.** A subgroup of the real symplectic
group `GLSymplectic ι ℝ` is maximal among its compact subgroups if and only if it is conjugate,
inside `GLSymplectic ι ℝ`, to the orthogonal symplectic matrices, that is, to the realified
unitary group `U(n)`. -/
theorem maximal_isCompact_iff {K : Subgroup (GLSymplectic ι ℝ)} :
    Maximal (fun H : Subgroup (GLSymplectic ι ℝ) ↦ IsCompact (H : Set (GLSymplectic ι ℝ))) K ↔
      ∃ g : GLSymplectic ι ℝ, K = MulAut.conj g •
        (unitarySubgroup (GL (ι ⊕ ι) ℝ)).subgroupOf (GLSymplectic ι ℝ) :=
  Subgroup.maximal_isCompact_iff_exists_eq_conj_smul maximal_isCompact_unitarySubgroup
    fun _ ↦ exists_conj_smul_le_unitarySubgroup

end TauCeti.GLSymplectic

end
