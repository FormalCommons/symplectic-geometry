/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.RepresentationTheory.InvariantForm

/-!
# Invariant forms under the adjoint automorphisms

A bilinear form `B` on the Lie algebra of a Lie group `G` that is invariant for the adjoint
representation is preserved by each adjoint automorphism `TauCeti.Lie.tangentAd g`, the Lie
algebra automorphism `Ad_g`: `B (Ad_g x) (Ad_g y) = B x y`. This restates
`TauCeti.Representation.IsInvariantForm.apply` for `Ad_g` read as `TauCeti.Lie.tangentAd g`, so
that a proof written with `tangentAd` need not pass through `adjointRepresentation`.

## Main results

* `TauCeti.Representation.IsInvariantForm.apply_tangentAd`: `B (Ad_g x) (Ad_g y) = B x y`.
-/

public section

namespace TauCeti.Representation.IsInvariantForm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I 1 G]
  [LieGroup I (minSmoothness 𝕜 3) G] {B : LinearMap.BilinForm 𝕜 (GroupLieAlgebra I G)}

/-- A form that is invariant for the adjoint representation is preserved by each adjoint
automorphism: `B (Ad_g x) (Ad_g y) = B x y`. -/
theorem apply_tangentAd (hB : IsInvariantForm (Lie.adjointRepresentation 𝕜 I G) B) (g : G)
    (x y : GroupLieAlgebra I G) :
    B (Lie.tangentAd (I := I) g x) (Lie.tangentAd (I := I) g y) = B x y := by
  rw [Lie.tangentAd_apply, Lie.tangentAd_apply, ← Lie.adjointRepresentation_apply (𝕜 := 𝕜),
    ← Lie.adjointRepresentation_apply (𝕜 := 𝕜), hB.apply]

end TauCeti.Representation.IsInvariantForm

end
