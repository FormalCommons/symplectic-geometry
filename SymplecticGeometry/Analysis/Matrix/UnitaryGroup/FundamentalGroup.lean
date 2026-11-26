/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Matrix.UnitaryGroup.Connected
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import TauCeti.Topology.Algebra.Matrix.UnitaryGroup
public import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange
import TauCeti.Topology.Algebra.UnitaryGroup
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Circle
import SymplecticGeometry.Analysis.Matrix.UnitaryGroup.Basic
import SymplecticGeometry.Topology.Grassmannian.StiefelFibration.Stability

/-!
# The fundamental group of the unitary group

For a nonempty finite index type `ι`, the determinant `Matrix.UnitaryGroup.detCircle` from the
complex unitary group `U(ι) = Matrix.unitaryGroup ι ℂ` to the unit circle induces an isomorphism
`π₁(U(ι), U) ≅ π₁(S¹, det U)`, at every base point `U`. Since `π₁(S¹) ≅ ℤ`
(`Circle.fundamentalGroupMulEquiv`), the fundamental group of `U(ι)` is infinite cyclic. As a
consequence the special unitary group `SU(ι) = Matrix.specialUnitaryGroup ι ℂ` is simply connected,
for every finite `ι`.

The proof goes by induction on `n = card ι`, for `ι = Fin n`. For `n = 1` the determinant is a
homeomorphism `U(1) ≃ S¹` (`Matrix.UnitaryGroup.detCircleEquivOfUnique`). The block embedding
`U(m) → U(1 + m)`, `B ↦ diag(1, B)`, is `2m`-connected
(`Matrix.UnitaryGroup.isNConnected_fromBlocksOne`), so it is bijective on `π₁` once `m ≥ 1`, and it
preserves the determinant; this carries the statement from `m` to `1 + m`. Path-connectedness of
`U(n)` moves the base point, and reindexing passes from `Fin (card ι)` to `ι`.

For `SU(ι)`, the map `A ↦ A · diag(1, …, star (det A), …, 1)` is a retraction of `U(ι)` onto
`SU(ι)` (Tau Ceti's `Matrix.UnitaryGroup.toSpecialUnitaryAt`).
A loop in `SU(ι)` has constant determinant, so it is null-homotopic in `U(ι)` by injectivity on
`π₁`, and the retraction carries this null-homotopy back into `SU(ι)`.

For an empty index type both groups are a point, so the fundamental group of `U(ι)` is trivial and
the determinant is not surjective on `π₁`: the hypothesis `Nonempty ι` cannot be dropped.

## Main results

* `Matrix.UnitaryGroup.bijective_fundamentalGroupMap_detCircle`: for nonempty `ι`, the determinant
  induces a bijection `π₁(U(ι), U) → π₁(S¹, det U)`.
* `Matrix.UnitaryGroup.fundamentalGroupMulEquivCircle`,
  `Matrix.UnitaryGroup.fundamentalGroupMulEquiv`:
  the resulting isomorphisms `π₁(U(ι), U) ≃* π₁(S¹, det U)` and `π₁(U(ι), U) ≃* ℤ`.
* `Matrix.UnitaryGroup.not_bijective_fundamentalGroupMap_detCircle_of_isEmpty`: the statement fails
  for empty `ι`.
* `Matrix.UnitaryGroup.homotopic_iff_angleChange_eq`: for every finite `ι`, two paths in `U(ι)`
  with the same ends are homotopic iff the determinant has the same angle change
  (`Circle.angleChange`) along them, from injectivity on `π₁` and
  `Circle.homotopic_iff_angleChange_map_eq`.
* `Matrix.instSimplyConnectedSpaceSpecialUnitaryGroup`: `SU(ι)` is simply connected.
* `Matrix.UnitaryGroup.bijective_fundamentalGroupMap_detCircle_and_simplyConnectedSpace`: for
  nonempty `ι`, three statements together: the determinant is bijective on `π₁` at every base
  point, `π₁(U(ι), U) ≃* ℤ`, and `SU(ι)` is simply connected.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.2.6.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 (the fibrations
  `U(n - 1) → U(n) → S^(2n-1)` and their long exact sequences).
-/

public section

open TauCeti

namespace Matrix.UnitaryGroup

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The case `ι = Fin n` of `bijective_homotopyGroupMap_detCircle`, by induction on `n ≥ 1`. -/
private theorem bijective_homotopyGroupMap_detCircle_fin (n : ℕ) (hn : 1 ≤ n)
    (U : unitaryGroup (Fin n) ℂ) :
    Function.Bijective (HomotopyGroup.map (N := Fin 1)
      (⟨detCircle, continuous_detCircle⟩ : C(unitaryGroup (Fin n) ℂ, Circle))
      (rfl : detCircle U = detCircle U)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    exact (HomotopyGroup.bijective_map_congr
      (ContinuousMap.ext fun V ↦ detCircleEquivOfUnique_apply V) _ _).1
      ((detCircleEquivOfUnique (Fin 1)).toHomeomorph.isWeakHomotopyEquivalence.map_bijective
        (Fin 1) U)
  | succ m hm ih =>
    let incl : C(unitaryGroup (Fin m) ℂ, unitaryGroup (Fin (1 + m)) ℂ) :=
      ⟨fromBlocksOne ℂ 1 m, continuous_fromBlocksOne m⟩
    have hincl := isNConnected_fromBlocksOne ℂ m (by rw [Complex.finrank_real_complex]; omega)
    rw [Complex.finrank_real_complex] at hincl
    have hinclb :
        Function.Bijective (HomotopyGroup.map (N := Fin 1) incl (rfl : incl 1 = incl 1)) :=
      ⟨hincl.injective 1 (by omega) 1, hincl.surjective 1 (by omega) 1⟩
    have hcomp := HomotopyGroup.map_comp_map_of_comp_eq (N := Fin 1) (x := 1)
      (g := (⟨detCircle, continuous_detCircle⟩ : C(unitaryGroup (Fin (1 + m)) ℂ, Circle)))
      (f := incl) (h := ⟨detCircle, continuous_detCircle⟩)
      (by ext B; simp [incl]) rfl rfl (detCircle_fromBlocksOne 1 1).symm
    have h1 : Function.Bijective (HomotopyGroup.map (N := Fin 1)
        (⟨detCircle, continuous_detCircle⟩ : C(unitaryGroup (Fin (1 + m)) ℂ, Circle))
        (rfl : detCircle (incl 1) = detCircle (incl 1))) := by
      rw [← Function.Bijective.of_comp_iff _ hinclb, hcomp]
      exact (HomotopyGroup.bijective_map_congr rfl _ _).1 (ih 1)
    revert U
    rw [add_comm m 1]
    exact fun V ↦ (ContinuousMap.bijective_map_iff_of_path _
      (PathConnectedSpace.somePath (incl 1) V)).1 h1

section Nonempty

variable [Nonempty ι]

/-- For a nonempty index type, `detCircle : U(ι) → S¹` induces a bijection on the first homotopy
group `π_ 1` at every base point. -/
theorem bijective_homotopyGroupMap_detCircle (U : unitaryGroup ι ℂ) :
    Function.Bijective (HomotopyGroup.map (N := Fin 1)
      (⟨detCircle, continuous_detCircle⟩ : C(unitaryGroup ι ℂ, Circle))
      (rfl : detCircle U = detCircle U)) := by
  let R := unitaryReindexContinuousMulEquiv ℂ (Fintype.equivFin ι)
  have hcomp := HomotopyGroup.map_comp_map_of_comp_eq (N := Fin 1) (x := U)
    (g := (⟨detCircle, continuous_detCircle⟩ :
      C(unitaryGroup (Fin (Fintype.card ι)) ℂ, Circle)))
    (f := (R.toHomeomorph : C(unitaryGroup ι ℂ, unitaryGroup (Fin (Fintype.card ι)) ℂ)))
    (h := ⟨detCircle, continuous_detCircle⟩)
    (ContinuousMap.ext fun V ↦ detCircle_unitaryReindexContinuousMulEquiv _ V) rfl rfl
    (detCircle_unitaryReindexContinuousMulEquiv _ U).symm
  have h := (bijective_homotopyGroupMap_detCircle_fin _ Fintype.card_pos (R U)).comp
    (R.toHomeomorph.isWeakHomotopyEquivalence.map_bijective (Fin 1) U)
  rw [hcomp] at h
  exact (HomotopyGroup.bijective_map_congr rfl _ _).1 h

/-- For a nonempty index type, `detCircle : U(ι) → S¹` induces a bijection of fundamental groups
`π₁(U(ι), U) → π₁(S¹, det U)` at every base point. -/
theorem bijective_fundamentalGroupMap_detCircle (U : unitaryGroup ι ℂ) :
    Function.Bijective (FundamentalGroup.map
      (⟨detCircle, continuous_detCircle⟩ : C(unitaryGroup ι ℂ, Circle)) U) := by
  simpa using (HomotopyGroup.bijective_map_iff_bijective_mapOfEq _ _).1
    (bijective_homotopyGroupMap_detCircle U)

variable (ι) in
/-- For a nonempty index type, the isomorphism `π₁(U(ι), U) ≃* π₁(S¹, det U)` induced by the
determinant `detCircle`. -/
noncomputable def fundamentalGroupMulEquivCircle (U : unitaryGroup ι ℂ) :
    FundamentalGroup (unitaryGroup ι ℂ) U ≃* FundamentalGroup Circle (detCircle U) :=
  MulEquiv.ofBijective _ (bijective_fundamentalGroupMap_detCircle U)

@[simp]
theorem fundamentalGroupMulEquivCircle_apply (U : unitaryGroup ι ℂ)
    (p : FundamentalGroup (unitaryGroup ι ℂ) U) :
    fundamentalGroupMulEquivCircle ι U p =
      FundamentalGroup.map (⟨detCircle, continuous_detCircle⟩ : C(unitaryGroup ι ℂ, Circle)) U p :=
  (rfl)

variable (ι) in
/-- For a nonempty index type, the fundamental group of `U(ι)` is infinite cyclic:
`π₁(U(ι), U) ≅ π₁(S¹, det U) ≅ ℤ`, the first isomorphism induced by the determinant and the second
`Circle.fundamentalGroupMulEquiv`. -/
noncomputable def fundamentalGroupMulEquiv (U : unitaryGroup ι ℂ) :
    FundamentalGroup (unitaryGroup ι ℂ) U ≃* Multiplicative ℤ :=
  (fundamentalGroupMulEquivCircle ι U).trans (Circle.fundamentalGroupMulEquiv _)

@[simp]
theorem fundamentalGroupMulEquiv_apply (U : unitaryGroup ι ℂ)
    (p : FundamentalGroup (unitaryGroup ι ℂ) U) :
    fundamentalGroupMulEquiv ι U p = Circle.fundamentalGroupMulEquiv _
      (FundamentalGroup.map
        (⟨detCircle, continuous_detCircle⟩ : C(unitaryGroup ι ℂ, Circle)) U p) :=
  (rfl)

end Nonempty

section IsEmpty

variable [IsEmpty ι]

/-- The hypothesis `Nonempty ι` of `bijective_fundamentalGroupMap_detCircle` is needed: for an
empty index type `U(ι)` is a point, so its trivial fundamental group cannot map onto
`π₁(S¹) ≅ ℤ`. -/
theorem not_bijective_fundamentalGroupMap_detCircle_of_isEmpty (U : unitaryGroup ι ℂ) :
    ¬ Function.Bijective (FundamentalGroup.map
      (⟨detCircle, continuous_detCircle⟩ : C(unitaryGroup ι ℂ, Circle)) U) :=
  fun h ↦ FundamentalGroup.not_surjective_map_circle_of_subsingleton U _ h.2

end IsEmpty

/-- **Paths in the unitary group are classified by the angle of the determinant.** Two paths
with the same ends in `U(ι)` are homotopic relative to their ends exactly when the determinant
turns through the same angle along them. This holds for every finite `ι`: for empty `ι` the group
is a point. -/
theorem homotopic_iff_angleChange_eq {U V : unitaryGroup ι ℂ} {δ δ' : Path U V} :
    δ.Homotopic δ' ↔ Circle.angleChange (δ.map continuous_detCircle) =
      Circle.angleChange (δ'.map continuous_detCircle) := by
  refine Circle.homotopic_iff_angleChange_map_eq (d := ⟨detCircle, continuous_detCircle⟩) ?_
  cases isEmpty_or_nonempty ι
  · exact Function.injective_of_subsingleton _
  · exact (bijective_fundamentalGroupMap_detCircle U).injective

end Matrix.UnitaryGroup

namespace Matrix

open UnitaryGroup

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem simplyConnectedSpace_specialUnitaryGroup_of_nonempty [Nonempty ι] :
    SimplyConnectedSpace (specialUnitaryGroup ι ℂ) := by
  let i₀ : ι := Classical.arbitrary ι
  let r : C(unitaryGroup ι ℂ, specialUnitaryGroup ι ℂ) :=
    ⟨toSpecialUnitaryAt i₀, continuous_toSpecialUnitaryAt i₀⟩
  let s : C(specialUnitaryGroup ι ℂ, unitaryGroup ι ℂ) :=
    ⟨Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup,
      continuous_inclusion specialUnitaryGroup_le_unitaryGroup⟩
  let d : C(unitaryGroup ι ℂ, Circle) := ⟨detCircle, continuous_detCircle⟩
  -- A special unitary matrix is its own correction.
  have hret (A : specialUnitaryGroup ι ℂ) : r (s A) = A :=
    Subtype.ext (toSpecialUnitaryAt_of_det_eq_one i₀ (mem_specialUnitaryGroup_iff.1 A.property).2)
  have hrs : r.comp s = ContinuousMap.id _ :=
    ContinuousMap.ext hret
  have : PathConnectedSpace (specialUnitaryGroup ι ℂ) :=
    Function.Surjective.pathConnectedSpace (f := r)
      (fun A ↦ ⟨s A, hret A⟩) r.continuous
  -- A loop in `SU(ι)` becomes, in `U(ι)`, a loop with constant determinant, so it is trivial in
  -- `π_1(U(ι))`; the retraction brings it back.
  have : Subsingleton (HomotopyGroup (Fin 1) (specialUnitaryGroup ι ℂ) 1) := by
    refine ⟨fun a b ↦ ?_⟩
    have key (c : HomotopyGroup (Fin 1) (specialUnitaryGroup ι ℂ) 1) :
        HomotopyGroup.map s (rfl : s 1 = s 1) c = 1 := by
      apply (bijective_homotopyGroupMap_detCircle (s 1)).1
      rw [HomotopyGroup.map_comp_apply, HomotopyGroup.map_one]
      have hds : d.comp s = ContinuousMap.const _ (detCircle (s 1)) :=
        ContinuousMap.ext fun A ↦ (detCircle_inclusion_specialUnitaryGroup A).trans
          (detCircle_inclusion_specialUnitaryGroup 1).symm
      exact (HomotopyGroup.map_congr hds _ rfl c).trans
        (HomotopyGroup.map_continuousMap_const_apply_eq_one _ _ _)
    have hr1 : r (s 1) = 1 := hret 1
    rw [← HomotopyGroup.map_map_of_comp_eq_id r s rfl hr1 hrs a,
      ← HomotopyGroup.map_map_of_comp_eq_id r s rfl hr1 hrs b, key, key]
  have : Subsingleton (FundamentalGroup (specialUnitaryGroup ι ℂ) 1) :=
    HomotopyGroup.pi1EquivFundamentalGroup.subsingleton_congr.1 this
  exact TauCeti.simplyConnectedSpace_of_subsingleton_fundamentalGroup 1

/-- The complex special unitary group `SU(ι)` is simply connected, for every finite index type
`ι`. For empty `ι` it is a point. -/
instance instSimplyConnectedSpaceSpecialUnitaryGroup :
    SimplyConnectedSpace (specialUnitaryGroup ι ℂ) := by
  cases isEmpty_or_nonempty ι
  · infer_instance
  · exact simplyConnectedSpace_specialUnitaryGroup_of_nonempty

end Matrix

namespace Matrix.UnitaryGroup

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **The fundamental group of the unitary group.** For a nonempty finite index type `ι` (that is,
`U(n)` with `n ≥ 1`), the determinant `detCircle : U(ι) → S¹` induces an isomorphism
`π₁(U(ι), U) ≅ π₁(S¹, det U)` at every base point, so `π₁(U(ι), U) ≅ ℤ`, and the special unitary
group `SU(ι)` is simply connected. For empty `ι` the first two claims fail
(`not_bijective_fundamentalGroupMap_detCircle_of_isEmpty`), while `SU(ι)` is still simply
connected (`Matrix.instSimplyConnectedSpaceSpecialUnitaryGroup`).

Milestone: *Fundamental group of the unitary group*. -/
theorem bijective_fundamentalGroupMap_detCircle_and_simplyConnectedSpace :
    (∀ U : unitaryGroup ι ℂ, Function.Bijective (FundamentalGroup.map
      (⟨detCircle, continuous_detCircle⟩ : C(unitaryGroup ι ℂ, Circle)) U)) ∧
    (∀ U : unitaryGroup ι ℂ,
      Nonempty (FundamentalGroup (unitaryGroup ι ℂ) U ≃* Multiplicative ℤ)) ∧
    SimplyConnectedSpace (specialUnitaryGroup ι ℂ) :=
  ⟨bijective_fundamentalGroupMap_detCircle, fun U ↦ ⟨fundamentalGroupMulEquiv ι U⟩,
    inferInstance⟩

end Matrix.UnitaryGroup

end
