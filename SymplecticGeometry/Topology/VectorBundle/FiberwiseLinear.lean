/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.FiberwiseLinear
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Trivializations followed by a fibrewise linear family

Let `e` be a local trivialization of a bundle with model fibre `F`, and `φ : B → F ≃L[𝕜] F` a
family of continuous linear automorphisms of `F` that, with its inverses, depends continuously on
the base point over an open set `U`. Following `e` by `(b, v) ↦ (b, φ b v)` gives a new local
trivialization `Bundle.Trivialization.transFiberwiseLinear`, with base set `e.baseSet ∩ U`. It is
`𝕜`-linear when `e` is. The fibrewise map is Mathlib's
`FiberwiseLinear.openPartialHomeomorph`.

This is how a local frame of a vector bundle is changed by a continuous family of matrices, for
instance a frame of a line bundle multiplied by a nowhere-zero continuous function.

## Main definitions

* `Bundle.Trivialization.transFiberwiseLinear`: the trivialization `e` followed by `φ`.

## Main results

* `Bundle.Trivialization.transFiberwiseLinear_apply`, `transFiberwiseLinear_symm_apply`: its
  forward and inverse maps.
* the instance `Bundle.Trivialization.isLinear_transFiberwiseLinear`: it is `𝕜`-linear when `e`
  is.
-/

public section

open Bundle Set

noncomputable section

namespace Bundle.Trivialization

variable {𝕜 B F Z : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace Z] {proj : Z → B}
  {U : Set B} {φ : B → F ≃L[𝕜] F}

/-- The local trivialization `e` followed by the fibrewise linear map `(b, v) ↦ (b, φ b v)`, where
`φ` and its inverses are continuous on the open set `U`. Its base set is `e.baseSet ∩ U`. -/
def transFiberwiseLinear (e : Trivialization F proj) (hU : IsOpen U)
    (hφ : ContinuousOn (fun x ↦ (φ x : F →L[𝕜] F)) U)
    (h2φ : ContinuousOn (fun x ↦ ((φ x).symm : F →L[𝕜] F)) U) : Trivialization F proj where
  toOpenPartialHomeomorph := (e.restrOpen U hU).toOpenPartialHomeomorph.trans
    (FiberwiseLinear.openPartialHomeomorph φ (e.open_baseSet.inter hU)
      (hφ.mono inter_subset_right) (h2φ.mono inter_subset_right))
  baseSet := e.baseSet ∩ U
  open_baseSet := e.open_baseSet.inter hU
  source_eq := by
    ext p
    simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hp, -⟩
      rwa [(e.restrOpen U hU).source_eq] at hp
    · intro hp
      have hp' : p ∈ (e.restrOpen U hU).source := by rwa [(e.restrOpen U hU).source_eq]
      refine ⟨hp', ?_⟩
      have := (e.restrOpen U hU).map_source hp'
      rw [(e.restrOpen U hU).target_eq] at this
      exact this
  target_eq := by
    ext ⟨b, v⟩
    simp only [OpenPartialHomeomorph.trans_target, mem_inter_iff, mem_preimage,
      (e.restrOpen U hU).target_eq]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h.1, mem_univ _⟩⟩
  proj_toFun p hp := by
    have hp' : p ∈ (e.restrOpen U hU).source := hp.1
    exact (e.restrOpen U hU).proj_toFun p hp'

variable (e : Trivialization F proj) (hU : IsOpen U)
  (hφ : ContinuousOn (fun x ↦ (φ x : F →L[𝕜] F)) U)
  (h2φ : ContinuousOn (fun x ↦ ((φ x).symm : F →L[𝕜] F)) U)

@[simp]
theorem transFiberwiseLinear_baseSet : (e.transFiberwiseLinear hU hφ h2φ).baseSet = e.baseSet ∩ U :=
  (rfl)

theorem transFiberwiseLinear_apply (p : Z) :
    e.transFiberwiseLinear hU hφ h2φ p = ((e p).1, φ (e p).1 (e p).2) :=
  (rfl)

theorem transFiberwiseLinear_symm_apply (b : B) (v : F) :
    (e.transFiberwiseLinear hU hφ h2φ).toOpenPartialHomeomorph.symm (b, v) =
      e.toOpenPartialHomeomorph.symm (b, (φ b).symm v) :=
  (rfl)

/-- At a point of the base set of `e`, the fibre coordinate of `e` followed by `φ` is `φ`
applied to the fibre coordinate of `e`. -/
@[simp]
theorem transFiberwiseLinear_apply_snd {E : B → Type*}
    [TopologicalSpace (TotalSpace F E)] (e : Trivialization F (π F E))
    (hφ : ContinuousOn (fun x ↦ (φ x : F →L[𝕜] F)) U)
    (h2φ : ContinuousOn (fun x ↦ ((φ x).symm : F →L[𝕜] F)) U) (b : B) (hb : b ∈ e.baseSet)
    (v : E b) :
    (e.transFiberwiseLinear hU hφ h2φ ⟨b, v⟩).2 = φ b (e ⟨b, v⟩).2 := by
  rw [transFiberwiseLinear_apply, e.coe_fst' hb]

/-- The trivialization `e` followed by a fibrewise `𝕜`-linear family is `𝕜`-linear when `e`
is. -/
instance isLinear_transFiberwiseLinear {E : B → Type*} [∀ b, AddCommMonoid (E b)]
    [∀ b, Module 𝕜 (E b)] [TopologicalSpace (TotalSpace F E)] (e : Trivialization F (π F E))
    [e.IsLinear 𝕜]
    (hφ : ContinuousOn (fun x ↦ (φ x : F →L[𝕜] F)) U)
    (h2φ : ContinuousOn (fun x ↦ ((φ x).symm : F →L[𝕜] F)) U) :
    (e.transFiberwiseLinear hU hφ h2φ).IsLinear 𝕜 where
  linear b hb := by
    have hb' : b ∈ e.baseSet := hb.1
    refine ⟨fun v w ↦ ?_, fun c v ↦ ?_⟩
    · simp only [e.transFiberwiseLinear_apply_snd hU hφ h2φ b hb', (e.linear 𝕜 hb').map_add,
        map_add]
    · simp only [e.transFiberwiseLinear_apply_snd hU hφ h2φ b hb', (e.linear 𝕜 hb').map_smul,
        map_smul]

end Bundle.Trivialization

end
