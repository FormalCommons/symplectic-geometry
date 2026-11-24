/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.InvariantForm
public import TauCeti.Geometry.Manifold.MFDeriv.Constancy
public import TauCeti.Geometry.Symplectic.Hamiltonian.SymplecticVectorField
import SymplecticGeometry.Geometry.Lie.FundamentalVectorField
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.DegreeOne

/-!
# Closed invariant forms on fundamental vector fields

Let a Lie group `G` act smoothly on a boundaryless manifold `M`, and let `γ` be a closed one-form
on `M` that is invariant under every `g • ·`. For each `ξ` in the Lie algebra of `G`, with
fundamental vector field `X_ξ`, the function `x ↦ γ_x(X_ξ x)` has zero differential, and so it is
constant when `M` is preconnected.

The proof is Cartan's formula `L_{X_ξ} γ = ι_{X_ξ} dγ + d (γ(X_ξ))`
(`TauCeti.mlieDerivForm_apply_eq_mextDeriv_add`): the left side vanishes by invariance
(`TauCeti.mlieDerivForm_fundamentalVectorField_eq_zero`), and the first term on the right by
closedness. It adapts the proof of Tau Ceti's
`TauCeti.mextDerivₗ_apply_fundamentalVectorField_eq_zero`, which applies the same formula with
the roles of the two terms exchanged.

For a closed invariant two-form `σ` the same invariance, through Tau Ceti's
`TauCeti.SmoothTwoForm.mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero`, makes every
fundamental vector field symplectic, so that `ι_{X_ξ} σ` is closed.

## Main results

* `TauCeti.mvfderiv_apply_fundamentalVectorField_eq_zero`: the pairing of a closed invariant
  one-form with a fundamental vector field has zero differential.
* `TauCeti.apply_fundamentalVectorField_eq_of_preconnectedSpace`: on a preconnected manifold this
  pairing is constant.
* `TauCeti.SmoothTwoForm.fundamental_toSectionLinearMap_mem_symplecticVectorFields` and
  `TauCeti.SmoothTwoForm.interiorₗ_fundamental_toSectionLinearMap_mem_closedForms`: for a closed
  invariant two-form `σ`, each fundamental vector field is symplectic and `ι_{X_ξ} σ` is closed.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], proof of
  Theorem 5.1.6.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  [T2Space G] [BoundarylessManifold I G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [T2Space M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If a closed one-form `γ` is invariant under every element of `G`, then for each `ξ` in the
Lie algebra of `G` the function `x ↦ γ_x(X_ξ x)`, which pairs `γ` with the fundamental vector
field of `ξ`, has zero differential at every point. -/
theorem mvfderiv_apply_fundamentalVectorField_eq_zero {γ : SmoothForm I' M F 1}
    (hγ : mextDeriv γ.val = 0)
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) γ = γ)
    (ξ : GroupLieAlgebra I G) (x : M) :
    mvfderiv I' (fun y ↦ γ.val y ![fundamentalVectorField I' ξ y]) x = 0 := by
  have hX : MDifferentiableAt I' I'.tangent
      (fun y ↦ (⟨y, fundamentalVectorField I' ξ y⟩ : TangentBundle I' M)) x :=
    (contMDiff_fundamentalVectorField (m := 1) (n := ∞) (by simp) ξ).mdifferentiableAt
      one_ne_zero
  ext v
  -- Cartan's formula: `0 = L_{X_ξ} γ = ι_{X_ξ} dγ + d(γ(X_ξ))`, and `dγ = 0`.
  have h := mlieDerivForm_apply_eq_mextDeriv_add (fun y ↦ rfl) (γ.mdifferentiableAt x) hX v
  rw [mlieDerivForm_fundamentalVectorField_eq_zero hinv ξ, hγ] at h
  simpa using (zero_add _).symm.trans h.symm

/-- On a preconnected manifold, a closed one-form `γ` invariant under every element of `G` pairs
the fundamental vector field of each `ξ` in the Lie algebra of `G` to a constant:
`γ_x(X_ξ x) = γ_y(X_ξ y)` for all `x` and `y`. -/
theorem apply_fundamentalVectorField_eq_of_preconnectedSpace [PreconnectedSpace M]
    {γ : SmoothForm I' M F 1} (hγ : mextDeriv γ.val = 0)
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) γ = γ)
    (ξ : GroupLieAlgebra I G) (x y : M) :
    γ.val x ![fundamentalVectorField I' ξ x] = γ.val y ![fundamentalVectorField I' ξ y] := by
  have hf := SmoothForm.contMDiff_apply_contMDiffSection γ
    ⟨_, contMDiff_fundamentalVectorField (m := ∞) (n := ∞) (by simp) ξ⟩
  refine (hf.mdifferentiable (by simp)).apply_eq_of_mfderiv_eq_zero (fun z ↦ ?_) x y
  exact mvfderiv_eq_zero_iff.mp (mvfderiv_apply_fundamentalVectorField_eq_zero hγ hinv ξ z)

/-- A closed two-form `σ` invariant under every element of `G` makes the fundamental vector field
of each `ξ` in the Lie algebra of `G` a symplectic vector field of `σ`. -/
theorem SmoothTwoForm.fundamental_toSectionLinearMap_mem_symplecticVectorFields
    {σ : SmoothTwoForm I' M} (hσ : σ.IsClosed)
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ)
    (ξ : GroupLieAlgebra I G) :
    (InfinitesimalAction.fundamental I G I' M).toSectionLinearMap ξ ∈ σ.symplecticVectorFields := by
  rw [SmoothTwoForm.mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero hσ,
    InfinitesimalAction.coe_fundamental_toSectionLinearMap]
  exact mlieDerivForm_fundamentalVectorField_eq_zero hinv ξ

/-- For a closed two-form `σ` invariant under every element of `G`, the contraction `ι_{X_ξ} σ`
with the fundamental vector field of each `ξ` in the Lie algebra of `G` is a closed one-form. -/
theorem SmoothTwoForm.interiorₗ_fundamental_toSectionLinearMap_mem_closedForms
    {σ : SmoothTwoForm I' M} (hσ : σ.IsClosed)
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ)
    (ξ : GroupLieAlgebra I G) :
    σ.interiorₗ ((InfinitesimalAction.fundamental I G I' M).toSectionLinearMap ξ) ∈
      closedForms I' M 1 := by
  rw [mem_closedForms, SmoothTwoForm.coe_interiorₗ]
  exact SmoothTwoForm.mem_symplecticVectorFields_iff.1
    (fundamental_toSectionLinearMap_mem_symplecticVectorFields hσ hinv ξ)

end TauCeti

end
