/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.Grassmannian.Lagrangian.Graph
public import TauCeti.Topology.Algebra.Group.Quotient.LocalSection
public import TauCeti.Topology.Homotopy.HurewiczFibration.LocallyTrivial
public import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle

/-!
# The unitary frame map `U(n) → ℒ(n)` is a fibration

Write `ℒ ι` for the space of Lagrangian subspaces of the standard model `(StdSpace ι, ω₀)` and
`unitaryFrame U = U • {y = 0}` for the Lagrangian framed by a unitary matrix `U`. Two unitary
matrices frame the same Lagrangian exactly when they differ on the right by a real orthogonal
matrix, so the fibres of `unitaryFrame` are the left cosets of `O(n)`, the subgroup
`Matrix.UnitaryGroup.realSubgroup ι`. This file shows that `unitaryFrame` is locally trivial with
fibre `O(n)`, hence has the homotopy lifting property and is a Serre fibration. In particular,
every path of Lagrangians lifts to a path of unitary matrices through any given starting frame
(Tau Ceti's `TauCeti.HasHomotopyLiftingProperty.exists_path_lift`, or
`TauCeti.TopCat.exists_path_lift_of_mem_serreFibrations`).

The local sections come from the basic chart `graphYChart`. A symmetric matrix `S` gives the
Lagrangian frame `fromRows S 1`, whose unitary matrix `unitaryOfFrame` frames the chart point
`graphY S` and depends continuously on `S`. This is a continuous section of `unitaryFrame` over
the Lagrangians transverse to `{y = 0}`, which contain `{x = 0}`. Every Lagrangian is `W • {x = 0}`
for a unitary `W`, and translating the section by `W` gives one around it. Tau Ceti's
`Subgroup.localSectionTrivializationOfCosetFibers` turns each such section into a trivialization.

## Main results

* `SymplecticGeometry.LagrangianGrassmannian.exists_trivialization_unitaryFrame`: every
  Lagrangian lies in the base set of a trivialization of `unitaryFrame` with fibre `O(n)`.
* `SymplecticGeometry.LagrangianGrassmannian.hasHomotopyLiftingProperty_unitaryFrame`:
  `unitaryFrame` has the homotopy lifting property with respect to every space.
* `SymplecticGeometry.LagrangianGrassmannian.unitaryFrame_mem_serreFibrations`: `unitaryFrame`
  is a Serre fibration, as a morphism of `TopCat`.

The construction follows Tau Ceti's unitary Stiefel fibration,
`TauCeti.exists_trivialization_unitaryFrameMap` and `TauCeti.unitaryFrameMap_mem_serreFibrations`
(`TauCeti/Topology/Grassmannian/StiefelFibration/Unitary.lean`), with the graph chart in place of
the Gram–Schmidt process.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.
-/

public section

namespace SymplecticGeometry

open Matrix TauCeti Set Topology
open scoped Pointwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "ℒ" ι => LagrangianGrassmannian (stdForm ι)

namespace LagrangianGrassmannian

/-- The unitary matrix of the Lagrangian frame `fromRows S 1` of a symmetric matrix `S`; it frames
the chart point `graphY S`. -/
private noncomputable def graphYUnitary (S : selfAdjoint (Matrix ι ι ℝ)) : unitaryGroup ι ℂ :=
  unitaryOfFrame (isLagrangian_range_fromRows_one (isHermitian_iff_isSymm.1 S.property))

private theorem unitaryFrame_graphYUnitary (S : selfAdjoint (Matrix ι ι ℝ)) :
    unitaryFrame (graphYUnitary S) = graphY S :=
  (graphY_eq_unitaryFrame S).symm

private theorem continuous_graphYUnitary :
    Continuous (graphYUnitary : selfAdjoint (Matrix ι ι ℝ) → unitaryGroup ι ℂ) :=
  continuous_unitaryOfFrame continuous_subtypeVal continuous_const _

/-- **Local triviality of the unitary frame map.** Every Lagrangian subspace of `StdSpace ι` lies
in the base set of a trivialization of `unitaryFrame : U(n) → ℒ ι` with fibre the orthogonal
group `O(n)`, the real unitary matrices. -/
theorem exists_trivialization_unitaryFrame (Λ : ℒ ι) :
    ∃ e : Bundle.Trivialization (UnitaryGroup.realSubgroup ι)
      (unitaryFrame : unitaryGroup ι ℂ → ℒ ι), Λ ∈ e.baseSet := by
  obtain ⟨W, rfl⟩ := MulAction.exists_smul_eq (unitaryGroup ι ℂ) (vertical ι) Λ
  let c : OpenPartialHomeomorph (ℒ ι) (selfAdjoint (Matrix ι ι ℝ)) := graphYChart
  let V : Set (ℒ ι) := W • c.source
  have hV : IsOpen V := c.open_source.smul W
  have hsec : ∀ Λ' ∈ V, unitaryFrame (W * graphYUnitary (c (W⁻¹ • Λ'))) = Λ' := fun Λ' h ↦ by
    rw [unitaryFrame_mul, unitaryFrame_graphYUnitary, ← graphYChart_symm_apply,
      c.left_inv (mem_smul_set_iff_inv_smul_mem.1 h), smul_inv_smul]
  have hs : ContinuousOn (fun Λ' ↦ W * graphYUnitary (c (W⁻¹ • Λ'))) V :=
    continuousOn_const.mul (continuous_graphYUnitary.comp_continuousOn
      (c.continuousOn.comp (continuous_const_smul _).continuousOn
        fun _ h ↦ mem_smul_set_iff_inv_smul_mem.1 h))
  refine ⟨Subgroup.localSectionTrivializationOfCosetFibers _ continuous_unitaryFrame
    (fun _ _ ↦ unitaryFrame_eq_unitaryFrame_iff) V hV _ hs hsec, ?_⟩
  rw [Subgroup.localSectionTrivializationOfCosetFibers_baseSet, smul_mem_smul_set_iff,
    ← graphY_zero, ← graphYChart_symm_apply]
  exact c.map_target (by simp [c])

variable (ι) in
/-- **The unitary frame map is a fibration.** The map `unitaryFrame : U(n) → ℒ ι` has the
homotopy lifting property with respect to every topological space `A`. -/
theorem hasHomotopyLiftingProperty_unitaryFrame (A : Type*) [TopologicalSpace A] :
    HasHomotopyLiftingProperty (unitaryFrame : unitaryGroup ι ℂ → ℒ ι) A :=
  hasHomotopyLiftingProperty_of_exists_trivialization exists_trivialization_unitaryFrame A

variable (ι) in
/-- The unitary frame map `U(n) → ℒ ι` is a Serre fibration, as a morphism of `TopCat`. -/
theorem unitaryFrame_mem_serreFibrations :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom ⟨unitaryFrame, continuous_unitaryFrame⟩ :
        _root_.TopCat.of (unitaryGroup ι ℂ) ⟶ _root_.TopCat.of (ℒ ι)) :=
  TopCat.mem_serreFibrations_of_exists_trivialization
    (F := UnitaryGroup.realSubgroup ι) exists_trivialization_unitaryFrame

end LagrangianGrassmannian

end SymplecticGeometry

end
