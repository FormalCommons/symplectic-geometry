/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.Topology

/-!
# Two-forms in the frame topology

Tau Ceti's frame topology on the sections of a vector bundle (`ContMDiffSection.frameTopology`)
is a topology on the `C^n` two-forms of a bundle `V`, since these are the sections of the bundle
of alternating maps on `V`. This file proves that nondegeneracy over a compact subset of the base
is an open condition in it, and that restricting two-forms on the tangent bundle to an open
subset is continuous for it.

## Main results

* `Bundle.ContMDiffTwoForm.isOpen_setOf_forall_mem_nondegenerate`: for a covering frame system,
  a locally compact model of the base, a bundle of finite rank and a compact `K ⊆ M`, the
  two-forms that are nondegenerate on every fibre over `K` form an open set.
* `Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_mpullback_subtypeVal`: for a covering
  frame system of the two-forms on `M` and any frame system of those on an open `U ⊆ M`, the
  restriction of two-forms on the tangent bundle from `M` to `U` is continuous.

## Implementation notes

The proof adapts Tau Ceti's
`IsCompact.isOpen_setOf_forall_mem_forall_bilinear_apply_self_pos`
(`TauCeti/Topology/VectorBundle/Bilinear.lean`), with nondegeneracy in place of positivity: the
nondegenerate alternating maps are open in the total space of the bundle of alternating maps
(`isOpen_setOf_nondegenerate`), evaluation is jointly continuous in the section and the point
(`ContMDiffSection.continuous_totalSpace_eval`), and the tube lemma over `K` concludes.

Restriction to `U` is Tau Ceti's `ContMDiffSection.continuous_restrict_frameTopology`, into the
sections of the pull-back of the bundle of two-forms along the inclusion `ι : U → M`, followed by
the fibrewise map `v ↦ v ∘ (dι × dι)` into the two-forms on the tangent bundle of `U`, which is
continuous by Tau Ceti's `ContMDiffSection.continuous_map_frameTopology`. That map is `C^∞` on
total spaces by `Bundle.Pullback.contMDiff_continuousAlternatingMap_totalSpace` and
`contMDiff_compContinuousLinearMap_totalSpace`, with the derivatives of `ι` as a section
(`Bundle.Pullback.contMDiff_mfderiv_hom`).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
  (symplectic vector bundles).
* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 2, §1 (the weak topology
  underlying the frame topology).
-/

public section

open Bundle TopologicalSpace
open scoped Manifold

namespace SymplecticGeometry

namespace Bundle.ContMDiffTwoForm

section Nondegenerate

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞}
  [IsManifold I n M] [ContMDiffVectorBundle n F V I]
  {ι : Type*}
  (e : ι → Trivialization (F [⋀^Fin 2]→L[ℝ] ℝ)
    (π (F [⋀^Fin 2]→L[ℝ] ℝ) (fun x ↦ V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- For a covering frame system, a locally compact model of the base and a bundle of finite
rank, the two-forms whose bilinear form is nondegenerate on the fibre over every point of a
compact set `K` form an open set in the frame topology. -/
theorem isOpen_setOf_forall_mem_nondegenerate [LocallyCompactSpace EB] [FiniteDimensional ℝ F]
    (hcover : ∀ x, ∃ i, x ∈ U i) {K : Set M} (hK : IsCompact K) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
    IsOpen {ω : ContMDiffTwoForm I n F V | ∀ x ∈ K, (ω.bilinFormAt x).Nondegenerate} := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  have hS := (isOpen_setOf_nondegenerate (F := F) (V := V)).preimage
    (ContMDiffSection.continuous_totalSpace_eval (I := I) (n := n) e U hU hcover)
  simp_rw [isOpen_iff_mem_nhds, bilinFormAt_def]
  exact fun ω hω ↦ hK.eventually_forall_of_forall_eventually fun x hx ↦ hS.mem_nhds (hω x hx)

end Nondegenerate

section Restriction

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  {U : Opens M} {ι κ : Type*}
  (e : ι → Trivialization (EB [⋀^Fin 2]→L[ℝ] ℝ)
    (π (EB [⋀^Fin 2]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (W : ι → Opens M) (hW : ∀ i, (W i : Set M) ⊆ (e i).baseSet)
  (e' : κ → Trivialization (EB [⋀^Fin 2]→L[ℝ] ℝ)
    (π (EB [⋀^Fin 2]→L[ℝ] ℝ) (fun x : U ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial U ℝ x)))
  [∀ j, MemTrivializationAtlas (e' j)]
  (W' : κ → Opens U) (hW' : ∀ j, (W' j : Set U) ⊆ (e' j).baseSet)

/-- Restriction of smooth two-forms on the tangent bundle from `M` to an open subset `U`, that is,
pull-back along the inclusion `U → M`, is continuous from the frame topology of a covering frame
system of the two-forms on `M` to the frame topology of any frame system of the two-forms on `U`,
when the model of `M` is finite-dimensional. -/
theorem continuous_tangentEquiv_symm_mpullback_subtypeVal (hcover : ∀ x, ∃ i, x ∈ W i) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e' W' hW'
    Continuous fun ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M)) ↦
      (tangentEquiv.symm (TauCeti.SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal
        (tangentEquiv ω)) : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := U))) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
  let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e' W' hW'
  let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  have hc : ContMDiff I I ((⊤ : ℕ∞) : WithTop ℕ∞) c := contMDiff_subtypeVal
  -- Read on the pull-back `c *ᵖ Λ²T*M`, restriction composes each value with `dι`.
  have hϕ := (contMDiff_compContinuousLinearMap_totalSpace (ι := Fin 2) (G := ℝ)
      (V₁ := (c : U → M) *ᵖ (TangentSpace I)) (V₂ := TangentSpace I (M := U)) _
      (Pullback.contMDiff_mfderiv_hom c hc)).comp
    (Pullback.contMDiff_continuousAlternatingMap_totalSpace (ι := Fin 2) (G := ℝ)
      (V := TangentSpace I (M := M)) c hc)
  let _ : ContMDiffVectorBundle ((⊤ : ℕ∞) : WithTop ℕ∞) (EB [⋀^Fin 2]→L[ℝ] ℝ)
      (c *ᵖ (fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)) I :=
    ContMDiffVectorBundle.pullback _ _ I
      (⟨Subtype.val, contMDiff_subtypeVal⟩ : C^((⊤ : ℕ∞) : WithTop ℕ∞)⟮I, U; I, M⟯)
  have h₁ := ContMDiffSection.continuous_restrict_frameTopology (I := I)
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW U
  have h₂ := ContMDiffSection.continuous_map_frameTopology
    (fun (x : U) (v : (c *ᵖ (fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)) x) ↦
      ContinuousAlternatingMap.compContinuousLinearMap
        (v : TangentSpace I (c x) [⋀^Fin 2]→L[ℝ] ℝ) (mfderiv I I c x)) hϕ
    (fun i ↦ (e i).pullback c) (fun i ↦ Opens.comap c (W i)) (fun i _ hx ↦ hW i hx)
    e' W' hW' (fun x ↦ hcover x)
  let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (fun i ↦ (e i).pullback c) (fun i ↦ Opens.comap c (W i)) (fun i _ hx ↦ hW i hx)
  refine (h₂.comp h₁).congr fun ω ↦ ?_
  ext x v
  rw [tangentEquiv_symm_apply, TauCeti.SmoothForm.mpullback_apply, tangentEquiv_apply,
    Function.comp_apply]
  -- The values of the sections on `U` lie in fibres of Mathlib's `Bundle.Pullback`, which is not
  -- reducible, so these evaluation lemmas match only up to unfolding it.
  erw [ContMDiffSection.map_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContMDiffSection.restrict_apply]
  simp only [Function.comp_def, c, ContinuousMap.coe_mk]

end Restriction

end Bundle.ContMDiffTwoForm

end SymplecticGeometry

end
