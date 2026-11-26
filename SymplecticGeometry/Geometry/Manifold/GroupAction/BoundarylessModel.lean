/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.ModelTransport.Interior

/-!
# Group actions on the boundaryless model of a manifold

Tau Ceti's `TauCeti.BoundarylessModel I M` is a copy of `M`, with the same carrier and topology;
when `M` is a boundaryless `C¹` manifold, the atlas
`TauCeti.BoundarylessModel.interiorChartedSpace` gives it charts in the model vector space `E`,
and `TauCeti.BoundarylessModel.interiorDiffeomorph` is the identity diffeomorphism from `M`.
This file carries an action of `G` on `M` to the copy, so that results proved for manifolds
modelled on a vector space apply to actions on boundaryless manifolds whose model may have
boundary.

## Main definitions and results

* `TauCeti.BoundarylessModel.instSMul`, `TauCeti.BoundarylessModel.instMulAction`: the copy
  inherits the scalar multiplication and the action of `G` on `M`, as it inherits Tau Ceti's
  monoid structure.
* `TauCeti.BoundarylessModel.homeomorph_smul`, `homeomorph_symm_smul`,
  `interiorDiffeomorph_smul` and `interiorDiffeomorph_symm_smul`: the identity maps commute with
  the actions.
* `TauCeti.BoundarylessModel.instContMDiffSMulInteriorChartedSpace`: a `C^n` scalar multiplication
  on `M` is a `C^n` scalar multiplication on the copy with its vector-space atlas.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.BoundarylessModel

variable {𝕜 E H M G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)

/-- The model copy inherits the scalar multiplication by `G` of the original space. -/
@[to_additive
  /-- The model copy inherits the additive scalar action of `G` on the original space. -/]
instance instSMul [SMul G M] : SMul G (BoundarylessModel I M) :=
  inferInstanceAs (SMul G M)

/-- The model copy inherits the action of `G` on the original space. -/
@[to_additive /-- The model copy inherits the additive action of `G` on the original space. -/]
instance instMulAction [Monoid G] [MulAction G M] : MulAction G (BoundarylessModel I M) :=
  inferInstanceAs (MulAction G M)

variable [TopologicalSpace M]

/-- The identity homeomorphism to the model copy commutes with the actions. -/
@[to_additive
  /-- The identity homeomorphism to the model copy commutes with the additive actions. -/]
theorem homeomorph_smul [SMul G M] (g : G) (x : M) :
    homeomorph I M (g • x) = g • homeomorph I M x := by
  rw [homeomorph_apply, homeomorph_apply]
  -- The action on the copy is that of `M`, by the definition of `instSMul`.
  rfl

/-- The inverse identity homeomorphism from the model copy commutes with the actions. -/
@[to_additive
  /-- The inverse identity homeomorphism from the model copy commutes with the additive
  actions. -/]
theorem homeomorph_symm_smul [SMul G M] (g : G) (x : BoundarylessModel I M) :
    (homeomorph I M).symm (g • x) = g • (homeomorph I M).symm x := by
  rw [homeomorph_symm_apply, homeomorph_symm_apply]
  -- The action on the copy is that of `M`, by the definition of `instSMul`.
  rfl

variable [ChartedSpace H M] [IsManifold I 1 M] [BoundarylessManifold I M]

attribute [local instance] interiorChartedSpace

/-- The identity diffeomorphism to the vector-space model copy commutes with the actions. -/
@[to_additive (attr := simp)
  /-- The identity diffeomorphism to the vector-space model copy commutes with the additive
  actions. -/]
theorem interiorDiffeomorph_smul [SMul G M] (n : ℕ∞ω) (g : G) (x : M) :
    interiorDiffeomorph I n (g • x) = g • interiorDiffeomorph I n x := by
  rw [coe_interiorDiffeomorph, homeomorph_smul]

/-- The inverse identity diffeomorphism from the vector-space model copy commutes with the
actions. -/
@[to_additive (attr := simp)
  /-- The inverse identity diffeomorphism from the vector-space model copy commutes with the
  additive actions. -/]
theorem interiorDiffeomorph_symm_smul [SMul G M] (n : ℕ∞ω) (g : G)
    (x : BoundarylessModel I M) :
    (interiorDiffeomorph I n).symm (g • x) = g • (interiorDiffeomorph I n).symm x := by
  rw [coe_interiorDiffeomorph_symm, homeomorph_symm_smul]

/-- A `C^n` scalar multiplication on a boundaryless manifold is a `C^n` scalar
multiplication on its copy with the vector-space atlas. -/
@[to_additive
  /-- A `C^n` additive scalar action on a boundaryless manifold is a `C^n` additive scalar
  action on its copy with the vector-space atlas. -/]
instance instContMDiffSMulInteriorChartedSpace {EG HG : Type*} [NormedAddCommGroup EG]
    [NormedSpace 𝕜 EG] [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG} [TopologicalSpace G]
    [ChartedSpace HG G] [SMul G M] {n : ℕ∞ω} [ContMDiffSMul IG I n G M] :
    ContMDiffSMul IG 𝓘(𝕜, E) n G (BoundarylessModel I M) where
  contMDiff_smul := by
    let Φ := interiorDiffeomorph I (M := M) n
    have h : (fun p : G × BoundarylessModel I M ↦ p.1 • p.2) =
        Φ ∘ (fun p : G × M ↦ p.1 • p.2) ∘ fun p ↦ (p.1, Φ.symm p.2) := by
      funext p
      rw [Function.comp_apply, Function.comp_apply, interiorDiffeomorph_smul,
        Diffeomorph.apply_symm_apply]
    rw [h]
    exact Φ.contMDiff.comp ((contMDiff_smul (I := IG) (I' := I)).comp
      (contMDiff_fst.prodMk (Φ.symm.contMDiff.comp contMDiff_snd)))

end TauCeti.BoundarylessModel

end
