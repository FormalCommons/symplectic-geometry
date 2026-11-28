/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic

/-!
# The tangent representation of a stabilizer preserving an almost complex structure

Let a group `G` act on a manifold `M` with an almost complex structure `J`, and let `x : M`.
Tau Ceti's `TauCeti.tangentRepresentation` lets an element `k` of the stabilizer of `x` act on
`T_x M` by the derivative `dk_x` of `k • ·` at `x`. If `dk_x` intertwines `J x` with `J (k • x)`,
that is, if `k` preserves `J` at `x`, then, since `k • x = x`, the operator `dk_x` commutes with
`J x` (`TauCeti.tangentRepresentation_apply_almostComplex`).

## Main results

* `TauCeti.tangentRepresentation_apply_almostComplex`: the tangent representation of an element
  of the stabilizer that preserves `J` at `x` commutes with `J x`.
-/

public section

open MulAction
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {G : Type*} [Group G] [MulAction G M] {x : M}

/-- **The stabilizer's differential commutes with `J x`.** If an element `k` of the stabilizer of
`x` preserves the almost complex structure `J` at `x`, in the sense that `dk_x ∘ J x` is
`J (k • x) ∘ dk_x`, then its tangent representation `dk_x` on `T_x M` commutes with `J x`. -/
theorem tangentRepresentation_apply_almostComplex {J : SmoothAlmostComplexStructure I M}
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I I (fun y : M ↦ g • y) x)
    {k : stabilizer G x}
    (hJ : ∀ v : TangentSpace I x, mfderiv I I (fun y : M ↦ (k : G) • y) x (J x v) =
      J ((k : G) • x) (mfderiv I I (fun y : M ↦ (k : G) • y) x v))
    (v : TangentSpace I x) :
    tangentRepresentation hd k (J x v) = J x (tangentRepresentation hd k v) := by
  have h := hJ v
  rw [show (k : G) • x = x from k.property] at h
  rw [tangentRepresentation_apply]
  exact h

end TauCeti

end
