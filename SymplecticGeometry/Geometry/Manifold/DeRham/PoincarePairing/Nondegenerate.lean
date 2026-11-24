/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing.Basic
import SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
import TauCeti.Geometry.Manifold.DeRham.CompactSupport

/-!
# Nondegeneracy of the Poincaré pairing in degrees `1` and `m - 1`

On a compact boundaryless oriented manifold `M` of dimension `m = 1 + l`, a closed `l`-form `β`
with `∫_M γ ∧ β = 0` for every closed one-form `γ` is exact. In other words, the Poincaré pairing
`H^1_dR(M) × H^l_c(M) → ℝ` (Tau Ceti's `TauCeti.poincarePairing`, where `H^l_c(M) = H^l_dR(M)` as
`M` is compact) is nondegenerate in its second argument.

The proof goes through the Hodge theorem rather than through singular homology. Choose a
Riemannian metric (`TauCeti.nonempty_contMDiffRiemannianMetric`) and write `β = η + dθ` with `η`
harmonic (`TauCeti.exists_mem_harmonicForms_sub_mem_exactForms`). The one-form `γ = ⋆η` is
harmonic, hence closed, and since the integral `∫_M γ ∧ β` depends only on the class of `β`,
`∫_M γ ∧ η = 0`. As `η = ± ⋆γ`, this says `∫_M |γ|² vol = 0`, so `γ = 0` by definiteness of the
`L²` pairing, hence `η = 0` and `β` is exact.

## Main results

* `TauCeti.integralTopForm_wedge_eq_of_sub_mem_exactForms_right`: on a closed oriented manifold,
  `∫_M γ ∧ β` for closed `γ` and `β` depends only on the de Rham class of `β`.
* `TauCeti.integralTopForm_wedge_eq_of_sub_mem_exactForms_left`: likewise, it depends only on the
  de Rham class of `γ`.
* `TauCeti.mem_exactForms_of_forall_integralTopForm_wedge_eq_zero`: a closed `l`-form on a closed
  oriented `(1 + l)`-manifold that integrates to zero against every closed one-form is exact.

## References

* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §6.
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §5.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

/-- On a compact boundaryless Hausdorff manifold with an orientation `o` of dimension `k + l`,
the integral `∫_M γ ∧ β` of a closed `k`-form `γ` against a closed `l`-form `β` depends only on
the de Rham class of `β`: it is unchanged when `β` is replaced by any `η` with `β - η` exact,
such an `η` being closed as well. -/
theorem integralTopForm_wedge_eq_of_sub_mem_exactForms_right
    [BoundarylessManifold I M] [T2Space M] [CompactSpace M] {k l : ℕ}
    (o : Manifold.Orientation I M (Fin (k + l))) {γ : SmoothForm I M ℝ k}
    (hγ : γ ∈ closedForms I M k) {β η : SmoothForm I M ℝ l} (hβ : β ∈ closedForms I M l)
    (hβη : β - η ∈ exactForms I M l) :
    integralTopForm o (RoughForm.wedge (γ : RoughForm I M ℝ k) (β : RoughForm I M ℝ l)) =
      integralTopForm o (RoughForm.wedge (γ : RoughForm I M ℝ k) (η : RoughForm I M ℝ l)) := by
  have hη : η ∈ closedForms I M l := by
    simpa using sub_mem hβ (exactForms_le_closedForms I l hβη)
  have hc {α : SmoothForm I M ℝ l} (hα : α ∈ closedForms I M l) :
      α ∈ compactlySupportedClosedForms I M l :=
    (mem_compactlySupportedClosedForms I).2 ⟨by simp [compactlySupportedForms_eq_top], hα⟩
  have hcls : compactlySupportedDeRhamCohomology.mk I l ⟨β, hc hβ⟩ =
      compactlySupportedDeRhamCohomology.mk I l ⟨η, hc hη⟩ := by
    rwa [compactlySupportedDeRhamCohomology.mk_eq_mk_iff,
      exactCompactlySupportedForms_eq_exactForms]
  rw [← poincarePairing_mk o ⟨γ, hγ⟩ ⟨β, hc hβ⟩, hcls, poincarePairing_mk]

/-- On a compact boundaryless Hausdorff manifold with an orientation `o` of dimension `k + l`,
the integral `∫_M γ ∧ β` of a closed `k`-form `γ` against a closed `l`-form `β` depends only on
the de Rham class of `γ`: it is unchanged when `γ` is replaced by any `δ` with `γ - δ` exact. -/
theorem integralTopForm_wedge_eq_of_sub_mem_exactForms_left
    [BoundarylessManifold I M] [T2Space M] [CompactSpace M] {k l : ℕ}
    (o : Manifold.Orientation I M (Fin (k + l))) {γ δ : SmoothForm I M ℝ k}
    (hγ : γ ∈ closedForms I M k) (hγδ : γ - δ ∈ exactForms I M k) {β : SmoothForm I M ℝ l}
    (hβ : β ∈ closedForms I M l) :
    integralTopForm o (RoughForm.wedge (γ : RoughForm I M ℝ k) (β : RoughForm I M ℝ l)) =
      integralTopForm o (RoughForm.wedge (δ : RoughForm I M ℝ k) (β : RoughForm I M ℝ l)) := by
  have hδ : δ ∈ closedForms I M k := by
    simpa using sub_mem hγ (exactForms_le_closedForms I k hγδ)
  have hc : β ∈ compactlySupportedClosedForms I M l :=
    (mem_compactlySupportedClosedForms I).2 ⟨by simp [compactlySupportedForms_eq_top], hβ⟩
  have hcls : deRhamCohomology.mk I k ⟨γ, hγ⟩ = deRhamCohomology.mk I k ⟨δ, hδ⟩ := by
    rw [← sub_eq_zero, ← map_sub, deRhamCohomology.mk_eq_zero_iff]
    exact hγδ
  rw [← poincarePairing_mk o ⟨γ, hγ⟩ ⟨β, hc⟩, hcls, poincarePairing_mk]

/-- **Nondegeneracy of the Poincaré pairing in degrees `(1, l)`**: on a compact boundaryless
Hausdorff manifold with an orientation `o` of dimension `1 + l`, a closed `l`-form `β` such that
`∫_M γ ∧ β = 0` for every closed one-form `γ` is exact. -/
theorem mem_exactForms_of_forall_integralTopForm_wedge_eq_zero
    [BoundarylessManifold I M] [T2Space M] [CompactSpace M] {l : ℕ}
    (o : Manifold.Orientation I M (Fin (1 + l))) {β : SmoothForm I M ℝ l}
    (hβ : β ∈ closedForms I M l)
    (h : ∀ γ ∈ closedForms I M 1,
      integralTopForm o (RoughForm.wedge (γ : RoughForm I M ℝ 1) (β : RoughForm I M ℝ l)) = 0) :
    β ∈ exactForms I M l := by
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤) (F := E)
    (E := fun x : M ↦ TangentSpace I x)
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle g
  have hl1 : l + 1 = 1 + l := Nat.add_comm l 1
  obtain ⟨η, hη, hβη⟩ := exists_mem_harmonicForms_sub_mem_exactForms o hl1 hβ
  -- The harmonic one-form `γ = ⋆η`, whose Hodge star is `(-1) ^ l • η`.
  set γ := SmoothForm.hodgeStar o hl1 η with hγ_def
  have hγ : γ ∈ closedForms I M 1 :=
    harmonicForms_le_closedForms o rfl (hodgeStar_mem_harmonicForms o hl1 rfl hη)
  have hγη : SmoothForm.hodgeStar o rfl γ = (-1 : ℝ) ^ l • η := by
    rw [hγ_def, SmoothForm.hodgeStar_hodgeStar, mul_one]
  -- The integral of `γ ∧ β` depends only on the class of `β`, so `∫ γ ∧ η = 0`.
  have hγη0 : integralTopForm o (RoughForm.wedge (γ : RoughForm I M ℝ 1)
      (η : RoughForm I M ℝ l)) = 0 :=
    (integralTopForm_wedge_eq_of_sub_mem_exactForms_right o hγ hβ hβη).symm.trans (h γ hγ)
  -- Hence `∫ |γ|² vol = 0`, so `γ = 0` and `η = 0`.
  have hγ0 : γ = 0 := by
    by_contra hγ0
    refine SmoothForm.integralTopForm_wedge_hodgeStar_self_ne_zero o rfl
      (by simp [compactlySupportedForms_eq_top]) hγ0 ?_
    rw [hγη, map_smul, map_smul, Submodule.coe_smul, integralTopForm_smul]
    simpa using hγη0
  have hη0 : η = 0 := by
    have := congrArg ((-1 : ℝ) ^ l • ·) hγη
    simpa [hγ0, smul_smul, ← mul_pow] using this.symm
  simpa [hη0] using hβη

end TauCeti

end
