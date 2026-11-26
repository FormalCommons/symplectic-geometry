/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Determinant
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# The determinant line of a line bundle

Let `E` be a vector bundle over a complete nontrivially normed field `𝕜` whose model `F` has
rank one. Its determinant line `TauCeti.DetBundle 𝕜 F E` has over `x` the fibre
`⋀[𝕜]^(finrank 𝕜 F) (E x)`, and in degree one the exterior power is the fibre itself
(`exteriorPower.oneEquiv`). This file shows that this identification is continuous in the base
point, so that a line bundle is its own determinant line.

In the chart induced by a linear trivialization `e` of `E`, the degree-one wedge of `v` has the
coordinate of `e v` in the basis `Module.finBasis 𝕜 F`
(`TauCeti.DetBundle.chartCoord_ιMulti`). So the identification reads, in the charts of `det E`
and of `E`, as `c ↦ c • b₀`, where `b₀` is the single vector of that basis
(`TauCeti.DetBundle.trivialization_oneEquiv`), and `TauCeti.bundleHomeomorph` gives the
homeomorphism.

The fibrewise equivalence `TauCeti.DetBundle.oneEquiv` is built as Tau Ceti's
`TauCeti.DetBundle.zeroEquiv` is in rank zero, by the same three-step composition. The proof of
continuity in `TauCeti.DetBundle.oneHomeomorph` adapts that of Tau Ceti's
`TauCeti.AssociatedBundle.continuous_detMap`: continuity is checked in charts with
`FiberBundle.continuous_of_forall_trivialization`, the chart coordinate of `det E` going to a
fixed multiple of the single basis vector.

## Main definitions and results

* `TauCeti.DetBundle.oneEquiv h x`: for a model of rank one, the continuous linear equivalence
  between the fibre of `det E` over `x` and `E x`, which sends the wedge of the single vector `v`
  to `v`.
* `TauCeti.DetBundle.oneHomeomorph h`: the homeomorphism of total spaces
  `TotalSpace 𝕜 (DetBundle 𝕜 F E) ≃ₜ TotalSpace F E` given by `oneEquiv h` on each fibre.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §3.
-/

public section

noncomputable section

open Bundle Module

namespace TauCeti.DetBundle

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- The linear equivalence underlying `TauCeti.DetBundle.oneEquiv`. -/
private def oneLinearEquiv (h : finrank 𝕜 F = 1) (x : B) : DetBundle 𝕜 F E x ≃ₗ[𝕜] E x :=
  (linearEquiv 𝕜 F E x).trans
    ((LinearEquiv.ofEq _ _ (congrArg (⋀[𝕜]^· (E x)) h)).trans (exteriorPower.oneEquiv 𝕜 (E x)))

variable (𝕜 F E) in
/-- When the model `F` has rank one, the fibre of the determinant line `det E` over `x`, the
exterior power of degree one of `E x`, is `E x` itself: this continuous linear equivalence sends
the wedge of a single vector `v` to `v` (`TauCeti.DetBundle.oneEquiv_ιMulti`). -/
def oneEquiv (h : finrank 𝕜 F = 1) (x : B) : DetBundle 𝕜 F E x ≃L[𝕜] E x :=
  haveI := VectorBundle.isTopologicalAddGroup 𝕜 F E x
  haveI := VectorBundle.continuousSMul 𝕜 F E x
  haveI := FiberBundle.t2Space F E x
  haveI := VectorBundle.finiteDimensional 𝕜 F E x
  { oneLinearEquiv h x with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (oneLinearEquiv h x).toLinearMap
    continuous_invFun := LinearMap.continuous_of_finiteDimensional
      (oneLinearEquiv h x).symm.toLinearMap }

/-- The image of a determinant vector under `TauCeti.DetBundle.oneEquiv`, through the
identification of the exterior powers of degrees `finrank 𝕜 F` and `1`. -/
theorem oneEquiv_apply (h : finrank 𝕜 F = 1) {x : B} (v : DetBundle 𝕜 F E x) :
    oneEquiv 𝕜 F E h x v = exteriorPower.oneEquiv 𝕜 (E x)
      (LinearEquiv.ofEq _ _ (congrArg (⋀[𝕜]^· (E x)) h) (linearEquiv 𝕜 F E x v)) :=
  (rfl)

/-- `TauCeti.DetBundle.oneEquiv` sends the wedge of a single vector `v` to `v`. -/
theorem oneEquiv_ιMulti (h : finrank 𝕜 F = 1) {x : B} (v : E x) :
    oneEquiv 𝕜 F E h x ((linearEquiv 𝕜 F E x).symm (exteriorPower.ιMulti 𝕜 _ fun _ ↦ v)) = v := by
  rw [oneEquiv_apply, LinearEquiv.apply_symm_apply, exteriorPower.ofEq_ιMulti h]
  exact exteriorPower.oneEquiv_ιMulti _

/-- The inverse of `TauCeti.DetBundle.oneEquiv` sends `v` to the wedge of `v` alone. -/
@[simp]
theorem oneEquiv_symm_apply (h : finrank 𝕜 F = 1) {x : B} (v : E x) :
    (oneEquiv 𝕜 F E h x).symm v =
      (linearEquiv 𝕜 F E x).symm (exteriorPower.ιMulti 𝕜 _ fun _ ↦ v) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, oneEquiv_ιMulti]

/-- **The identification in charts.** For a linear trivialization `e` of `E` whose model has
rank one, the coordinate in `e` of the image under `TauCeti.DetBundle.oneEquiv` of a determinant
vector `v` is the chart coordinate of `v` times the single vector of `Module.finBasis 𝕜 F`. -/
theorem trivialization_oneEquiv (h : finrank 𝕜 F = 1) (e : Trivialization F (π F E))
    [e.IsLinear 𝕜] {x : B} (hx : x ∈ e.baseSet) (v : DetBundle 𝕜 F E x) :
    (e ⟨x, oneEquiv 𝕜 F E h x v⟩).2 =
      chartCoord e hx v • Module.finBasis 𝕜 F (Fin.cast h.symm 0) := by
  let : Unique (Fin (finrank 𝕜 F)) := h ▸ Fin.instUnique
  obtain ⟨w, rfl⟩ := (oneEquiv 𝕜 F E h x).symm.surjective v
  rw [ContinuousLinearEquiv.apply_symm_apply, oneEquiv_symm_apply, chartCoord_ιMulti,
    Subsingleton.elim (Fin.cast h.symm 0) default]
  exact ((Module.finBasis 𝕜 F).det_unique_smul fun _ ↦ (e ⟨x, w⟩).2).symm

variable (𝕜 F E) in
/-- **A line bundle is its own determinant line.** When the model `F` has rank one, the total
space of the determinant line `TauCeti.DetBundle 𝕜 F E` is homeomorphic to that of `E`, by
`TauCeti.DetBundle.oneEquiv` on each fibre. -/
def oneHomeomorph (h : finrank 𝕜 F = 1) : TotalSpace 𝕜 (DetBundle 𝕜 F E) ≃ₜ TotalSpace F E :=
  bundleHomeomorph (oneEquiv 𝕜 F E h) <| by
    refine FiberBundle.continuous_of_forall_trivialization _ (fun _ ↦ rfl) fun p ↦ ?_
    set t := trivializationAt F E p.proj
    refine ⟨trivializationAt 𝕜 (DetBundle 𝕜 F E) p.proj, t,
      fun _ c ↦ c • Module.finBasis 𝕜 F (Fin.cast h.symm 0),
      mem_baseSet_trivializationAt 𝕜 _ p.proj, mem_baseSet_trivializationAt F E p.proj,
      ((trivializationAt 𝕜 (DetBundle 𝕜 F E) p.proj).continuousOn.continuousAt
        ((trivializationAt 𝕜 (DetBundle 𝕜 F E) p.proj).open_source.mem_nhds
          (FiberBundle.mem_trivializationAt_proj_source))).snd.smul continuousAt_const, ?_⟩
    rintro ⟨x, v⟩ (hx : x ∈ (trivializationAt 𝕜 (DetBundle 𝕜 F E) p.proj).baseSet) -
    rw [trivializationAt_eq, trivialization_baseSet] at hx
    rw [trivializationAt_eq, trivialization_apply_mk _ hx]
    exact trivialization_oneEquiv h t hx v

@[simp]
theorem oneHomeomorph_apply (h : finrank 𝕜 F = 1) (p : TotalSpace 𝕜 (DetBundle 𝕜 F E)) :
    oneHomeomorph 𝕜 F E h p = ⟨p.proj, oneEquiv 𝕜 F E h p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp]
theorem oneHomeomorph_symm_apply (h : finrank 𝕜 F = 1) (p : TotalSpace F E) :
    (oneHomeomorph 𝕜 F E h).symm p = ⟨p.proj, (oneEquiv 𝕜 F E h p.proj).symm p.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ p

end TauCeti.DetBundle

end
