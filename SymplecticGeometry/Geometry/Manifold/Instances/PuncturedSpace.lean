/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import TauCeti.Geometry.Manifold.Instances.Cylinder
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Maps of punctured spaces induced by injective linear maps

An injective continuous linear map `L : V →L[R] W` sends nonzero vectors to nonzero vectors, so
it restricts to a map `TauCeti.puncturedSpace.map L hL` from Tau Ceti's punctured space
`TauCeti.puncturedSpace V = V ∖ {0}` to `TauCeti.puncturedSpace W`.

* `TauCeti.puncturedSpace.map_def`, `TauCeti.puncturedSpace.coe_map`: the map sends `v` to
  `L v`; it takes the identity to the identity and composites to composites (`map_id`,
  `map_comp`).
* `TauCeti.puncturedSpace.contMDiff_map`: over a nontrivially normed field `𝕜`, the map is `C^n`
  for every `n : ℕ∞ω`, by Tau Ceti's `TauCeti.ContMDiff.subtypeVal_comp_iff`.
* `TauCeti.puncturedSpace.mfderiv_map`: its derivative at every point is `L` itself, with the
  pointwise form `mfderiv_map_apply`, by Tau Ceti's
  `TauCeti.Manifold.mfderiv_apply_of_subtype_val_comp_eq`.
-/

public section

open Function
open scoped Manifold ContDiff

namespace TauCeti.puncturedSpace

section Map

variable {R V W : Type*} [Semiring R] [AddCommMonoid V] [Module R V] [TopologicalSpace V]
  [T1Space V] [AddCommMonoid W] [Module R W] [TopologicalSpace W] [T1Space W]

/-- The map `V ∖ {0} → W ∖ {0}`, `v ↦ L v`, induced by an injective continuous linear map
`L : V →L[R] W`. -/
def map (L : V →L[R] W) (hL : Injective L) (v : puncturedSpace V) : puncturedSpace W :=
  ⟨L v, mem_puncturedSpace.2 ((map_ne_zero_iff L hL).2 (mem_puncturedSpace.1 v.property))⟩

theorem map_def (L : V →L[R] W) (hL : Injective L) (v : puncturedSpace V) :
    map L hL v =
      ⟨L v, mem_puncturedSpace.2 ((map_ne_zero_iff L hL).2 (mem_puncturedSpace.1 v.property))⟩ :=
  (rfl)

/-- The map of punctured spaces induced by `L` sends `v` to `L v`. -/
@[simp]
theorem coe_map (L : V →L[R] W) (hL : Injective L) (v : puncturedSpace V) :
    (map L hL v : W) = L v :=
  (rfl)

/-- The map of punctured spaces induced by `L` is the restriction of `L`. -/
theorem subtypeVal_comp_map (L : V →L[R] W) (hL : Injective L) :
    Subtype.val ∘ map L hL = L ∘ Subtype.val :=
  funext (coe_map L hL)

/-- The identity induces the identity of the punctured space. -/
@[simp]
theorem map_id :
    map (ContinuousLinearMap.id R V) (by rw [ContinuousLinearMap.coe_id']; exact injective_id) =
      id :=
  funext fun v ↦ Subtype.ext <| by rw [coe_map, ContinuousLinearMap.id_apply, id_eq]

/-- The map of punctured spaces induced by a composite is the composite of the induced maps. -/
theorem map_comp {U : Type*} [AddCommMonoid U] [Module R U] [TopologicalSpace U] [T1Space U]
    (L₂ : V →L[R] W) (hL₂ : Injective L₂) (L₁ : U →L[R] V) (hL₁ : Injective L₁) :
    map (L₂.comp L₁) (by rw [ContinuousLinearMap.coe_comp]; exact hL₂.comp hL₁) =
      map L₂ hL₂ ∘ map L₁ hL₁ :=
  funext fun v ↦ Subtype.ext <| by
    rw [Function.comp_apply, coe_map, coe_map, coe_map, ContinuousLinearMap.comp_apply]

end Map

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The map of punctured spaces induced by an injective continuous linear map is `C^n`. -/
theorem contMDiff_map (L : V →L[𝕜] W) (hL : Injective L) (n : ℕ∞ω) :
    ContMDiff 𝓘(𝕜, V) 𝓘(𝕜, W) n (map L hL) :=
  (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1 <| by
    rw [subtypeVal_comp_map]
    exact L.contMDiff.comp contMDiff_subtypeVal

/-- The derivative of the map of punctured spaces induced by `L`, at any point, sends a tangent
vector `u` to `L u`. -/
theorem mfderiv_map_apply (L : V →L[𝕜] W) (hL : Injective L) (v : puncturedSpace V)
    (u : TangentSpace 𝓘(𝕜, V) v) :
    mfderiv 𝓘(𝕜, V) 𝓘(𝕜, W) (map L hL) v u = L u := by
  have h := TauCeti.Manifold.mfderiv_apply_of_subtype_val_comp_eq (I := 𝓘(𝕜, V))
    (I' := 𝓘(𝕜, W)) (subtypeVal_comp_map L hL) u
  rwa [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at h

/-- The derivative of the map of punctured spaces induced by `L` is `L`, at every point. -/
theorem mfderiv_map (L : V →L[𝕜] W) (hL : Injective L) (v : puncturedSpace V) :
    mfderiv 𝓘(𝕜, V) 𝓘(𝕜, W) (map L hL) v = L :=
  ContinuousLinearMap.ext (mfderiv_map_apply L hL v)

end TauCeti.puncturedSpace

end
