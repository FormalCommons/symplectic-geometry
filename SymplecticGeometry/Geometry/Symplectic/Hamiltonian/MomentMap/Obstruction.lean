/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Algebra.Lie.Cohomology.TwoCocycle
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic

/-!
# The cohomological obstruction to an equivariant moment map

Let `a : Z ↦ Z_M` be an infinitesimal action of a real Lie algebra `𝔤` on a manifold `M` with a
closed two-form `σ`, and `μ : M → 𝔤*` a moment map of `a` in Tau Ceti's sign
(`TauCeti.SmoothTwoForm.IsMomentMap`). Tau Ceti shows that the cocycle
`c(Z, Z') = σ(Z_M, Z'_M) - μ_{⁅Z, Z'⁆}` of `μ` (`TauCeti.SmoothTwoForm.momentCocycle`) is a Lie
algebra `2`-cocycle with trivial coefficients at every point, and constant on a preconnected
manifold. This file takes its class in the second Lie algebra cohomology
`TauCeti.LieModule.Cohomology.cohomology ℝ 𝔤 (TrivialLieModule ℝ 𝔤 ℝ) 2`
(`TauCeti.SmoothTwoForm.IsMomentMap.cohomologyClass`), and proves:

* on a preconnected manifold, the class depends neither on the point nor on the moment map, since
  two moment maps differ by a constant `ν`, which changes the cocycle by the coboundary `d ν`;
* the class vanishes exactly when a constant shift `μ + ν` has cocycle zero;
* for the fundamental vector fields of a symplectic action of a connected Lie group on a connected
  manifold, the class vanishes exactly when a constant shift of `μ` is coadjoint-equivariant
  (by Tau Ceti's `IsMomentMap.isEquivariantMomentMap_of_momentCocycle_eq_zero` and
  `IsEquivariantMomentMap.momentCocycle_eq_zero`).

The milestone `SymplecticGeometry.equivariantMomentMap_obstruction` collects these statements in
the Hamiltonian sign `ι_{X_H} ω = -dH` of the library, where a moment map `μ` is one for which
`fun x ↦ -μ x` is a moment map in Tau Ceti's sign, and its cocycle is that of `fun x ↦ -μ x`.

## Main definitions

* `TauCeti.SmoothTwoForm.IsMomentMap.cohomologyClass`: the class in `H²(𝔤; ℝ)` of the cocycle of a
  moment map at a point.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.cohomologyClass_eq_of_isMomentMap`: on a preconnected
  manifold, any two moment maps have the same class.
* `TauCeti.SmoothTwoForm.IsMomentMap.cohomologyClass_eq_zero_iff`: the class vanishes exactly
  when a constant shift of the moment map has cocycle zero.
* `TauCeti.SmoothTwoForm.IsMomentMap.cohomologyClass_eq_zero_iff_exists_isEquivariantMomentMap`:
  for a symplectic action of a connected Lie group on a connected manifold, the class vanishes
  exactly when a constant shift of the moment map is equivariant.
* `SymplecticGeometry.equivariantMomentMap_obstruction`: the milestone, in the library's sign.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemmas 5.2.1 and 5.2.3.
-/

public section

open scoped Manifold ContDiff

open LieModule.Cohomology TauCeti.LieModule.Cohomology

namespace TauCeti.SmoothTwoForm.IsMomentMap

section Infinitesimal

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ μ' : M → Module.Dual ℝ 𝔤}

/-- The **cohomology class** of a moment map `μ` of a closed two-form at a point `x`: the class of
its cocycle `σ.momentCocycle a μ x` in the second Lie algebra cohomology `H²(𝔤; ℝ)` with trivial
coefficients. On a preconnected manifold it depends neither on `x`
(`IsMomentMap.cohomologyClass_eq`) nor on `μ` (`IsMomentMap.cohomologyClass_eq_of_isMomentMap`). -/
noncomputable def cohomologyClass (h : σ.IsMomentMap a μ) (hσ : σ.IsClosed) (x : M) :
    cohomology ℝ 𝔤 (TrivialLieModule ℝ 𝔤 ℝ) 2 :=
  twoCocycleClass ℝ 𝔤 _ (σ.momentCocycle a μ x) (h.momentCocycle_mem_twoCocycle hσ x)

/-- The class of a moment map at `x` is the class of its cocycle at `x`. -/
theorem cohomologyClass_def (h : σ.IsMomentMap a μ) (hσ : σ.IsClosed) (x : M) :
    h.cohomologyClass hσ x =
      twoCocycleClass ℝ 𝔤 _ (σ.momentCocycle a μ x) (h.momentCocycle_mem_twoCocycle hσ x) :=
  (rfl)

/-- On a preconnected manifold, the class of a moment map does not depend on the point. -/
theorem cohomologyClass_eq [PreconnectedSpace M] (h : σ.IsMomentMap a μ) (hσ : σ.IsClosed)
    (x x' : M) : h.cohomologyClass hσ x = h.cohomologyClass hσ x' := by
  rw [cohomologyClass_def, cohomologyClass_def]
  congr 1
  exact h.momentCocycle_eq hσ x x'

/-- Shifting a moment map by a constant does not change its class. -/
theorem cohomologyClass_add_const (h : σ.IsMomentMap a μ) (hσ : σ.IsClosed)
    (ν : Module.Dual ℝ 𝔤) (x : M) :
    (h.add_const ν).cohomologyClass hσ x = h.cohomologyClass hσ x := by
  rw [cohomologyClass_def, cohomologyClass_def, twoCocycleClass_eq_iff]
  exact ⟨_, momentCocycle_add_const σ a μ ν x⟩

/-- **The class does not depend on the moment map.** On a preconnected manifold, any two moment
maps of an action for a closed two-form have the same class, at any two points. -/
theorem cohomologyClass_eq_of_isMomentMap [PreconnectedSpace M] (h : σ.IsMomentMap a μ)
    (h' : σ.IsMomentMap a μ') (hσ : σ.IsClosed) (x x' : M) :
    h'.cohomologyClass hσ x = h.cohomologyClass hσ x' := by
  obtain ⟨ν, rfl⟩ := h.isMomentMap_iff_exists_eq_add.1 h'
  exact (h.cohomologyClass_add_const hσ ν x).trans (h.cohomologyClass_eq hσ x x')

/-- The class of a moment map vanishes exactly when a constant shift `μ + ν` of it has cocycle
zero at `x`. -/
theorem cohomologyClass_eq_zero_iff (h : σ.IsMomentMap a μ) (hσ : σ.IsClosed) (x : M) :
    h.cohomologyClass hσ x = 0 ↔
      ∃ ν : Module.Dual ℝ 𝔤, σ.momentCocycle a (fun y ↦ μ y + ν) x = 0 := by
  rw [cohomologyClass_def, twoCocycleClass_eq_zero_iff]
  set e := TrivialLieModule.equiv ℝ 𝔤 ℝ
  refine ⟨fun ⟨f, hf⟩ ↦ ⟨-(e.toLinearMap ∘ₗ f), ?_⟩, fun ⟨ν, hν⟩ ↦
    ⟨-(e.symm.toLinearMap ∘ₗ ν), ?_⟩⟩
  · have hf' : e.symm.toLinearMap ∘ₗ (-(e.toLinearMap ∘ₗ f)) = -f := by
      ext Z
      simp
    rw [momentCocycle_add_const, hf', map_neg, hf, add_neg_cancel]
  · rw [momentCocycle_add_const] at hν
    rw [map_neg, neg_eq_iff_add_eq_zero, add_comm, hν]

end Infinitesimal

end TauCeti.SmoothTwoForm.IsMomentMap

section Group

open TauCeti TauCeti.SmoothTwoForm

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

-- Tau Ceti's equivariant moment maps are stated for a `C^{minSmoothness ℝ 3}` Lie group.
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace TauCeti.SmoothTwoForm.IsMomentMap

/-- **The obstruction to an equivariant moment map.** Let a connected Lie group act on a connected
manifold, preserving a closed two-form. A moment map of the action by fundamental vector fields has
class zero exactly when a constant shift of it is coadjoint-equivariant. -/
theorem cohomologyClass_eq_zero_iff_exists_isEquivariantMomentMap [PreconnectedSpace G]
    [PreconnectedSpace M] (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : σ.IsClosed) (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) (x : M) :
    h.cohomologyClass hσ x = 0 ↔
      ∃ ν : Module.Dual ℝ (GroupLieAlgebra I G), σ.IsEquivariantMomentMap fun y ↦ μ y + ν := by
  rw [h.cohomologyClass_eq_zero_iff]
  exact ⟨fun ⟨ν, hν⟩ ↦ ⟨ν, (h.add_const ν).isEquivariantMomentMap_of_momentCocycle_eq_zero hG hν⟩,
    fun ⟨ν, hν⟩ ↦ ⟨ν, hν.momentCocycle_eq_zero x⟩⟩

end TauCeti.SmoothTwoForm.IsMomentMap

namespace SymplecticGeometry

/-- **Equivariance and the obstruction to an equivariant moment map**, in the Hamiltonian sign
`ι_{X_H} σ = -dH`. Let a Lie group `G` act on a connected manifold `M`, preserving a closed
two-form `σ`, and let `μ : M → 𝔤*` be a moment map in this sign: `fun x ↦ -μ x` is a moment map
of the fundamental vector fields in Tau Ceti's sign. Its cocycle, the cocycle `τ` of
`fun x ↦ -μ x`, then

1. is the same at all points of `M`;
2. is a Lie algebra `2`-cocycle with trivial coefficients;
3. has a class in `H²(𝔤; ℝ)` that is the same for every moment map `μ'`;
4. has class zero exactly when some constant shift `μ + ν` has cocycle zero at every point;
5. vanishes if `μ` is equivariant;
6. for connected `G`, makes `μ` equivariant if it vanishes at one point;

so that, for connected `G`, the class is zero exactly when some constant shift of `μ` is
equivariant.

Milestone: *Equivariance and the obstruction to an equivariant moment map*. -/
theorem equivariantMomentMap_obstruction [PreconnectedSpace M] (hσ : σ.IsClosed)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x) :
    (∀ x x', σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) (fun y ↦ -μ y) x =
        σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) (fun y ↦ -μ y) x') ∧
      (∀ x, σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) (fun y ↦ -μ y) x ∈
        twoCocycle ℝ (GroupLieAlgebra I G) (TrivialLieModule ℝ (GroupLieAlgebra I G) ℝ)) ∧
      (∀ (μ' : M → Module.Dual ℝ (GroupLieAlgebra I G))
        (h' : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ' x) (x x' : M),
        h'.cohomologyClass hσ x' = h.cohomologyClass hσ x) ∧
      (∀ x, h.cohomologyClass hσ x = 0 ↔ ∃ ν : Module.Dual ℝ (GroupLieAlgebra I G),
        ∀ y, σ.momentCocycle (InfinitesimalAction.fundamental I G I' M)
          (fun z ↦ -(μ z + ν)) y = 0) ∧
      (σ.IsEquivariantMomentMap (fun x ↦ -μ x) →
        ∀ x, σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) (fun y ↦ -μ y) x = 0) ∧
      (PreconnectedSpace G → ∀ x,
        σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) (fun y ↦ -μ y) x = 0 →
          σ.IsEquivariantMomentMap fun x ↦ -μ x) ∧
      (PreconnectedSpace G → ∀ x, h.cohomologyClass hσ x = 0 ↔
        ∃ ν : Module.Dual ℝ (GroupLieAlgebra I G),
          σ.IsEquivariantMomentMap fun y ↦ -(μ y + ν)) := by
  have hshift (ν : Module.Dual ℝ (GroupLieAlgebra I G)) :
      (fun y ↦ -(μ y + -ν)) = fun y ↦ -μ y + ν := funext fun y ↦ by rw [neg_add, neg_neg]
  refine ⟨h.momentCocycle_eq hσ, h.momentCocycle_mem_twoCocycle hσ,
    fun μ' h' x x' ↦ h.cohomologyClass_eq_of_isMomentMap h' hσ x' x, fun x ↦ ?_,
    fun hμ x ↦ hμ.momentCocycle_eq_zero x,
    fun _ x hx ↦ h.isEquivariantMomentMap_of_momentCocycle_eq_zero hG hx, fun _ x ↦ ?_⟩
  · rw [h.cohomologyClass_eq_zero_iff]
    refine ⟨fun ⟨ν, hν⟩ ↦ ⟨-ν, fun y ↦ ?_⟩, fun ⟨ν, hν⟩ ↦ ⟨-ν, ?_⟩⟩
    · rw [hshift, (h.add_const ν).momentCocycle_eq hσ y x, hν]
    · simpa only [neg_add] using hν x
  · rw [h.cohomologyClass_eq_zero_iff_exists_isEquivariantMomentMap hσ hG]
    refine ⟨fun ⟨ν, hν⟩ ↦ ⟨-ν, ?_⟩, fun ⟨ν, hν⟩ ↦ ⟨-ν, ?_⟩⟩
    · rwa [hshift]
    · simpa only [neg_add] using hν

end SymplecticGeometry

end Group

end
