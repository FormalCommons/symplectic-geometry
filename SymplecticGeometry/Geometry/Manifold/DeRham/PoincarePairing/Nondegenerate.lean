/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing.Basic
import SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

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

* `TauCeti.exactCompactlySupportedForms_eq_exactForms`: on a compact manifold, every exact form is
  the exterior derivative of a compactly supported form.
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

section CompactSupport

variable [IsManifold I 2 M]

variable (I M) in
/-- On a compact manifold every exact form is the exterior derivative of a compactly supported
form, since every form is compactly supported. -/
theorem exactCompactlySupportedForms_eq_exactForms [CompactSpace M] (k : ℕ) :
    exactCompactlySupportedForms I M k = exactForms I M k := by
  cases k with
  | zero => rw [exactCompactlySupportedForms_zero, exactForms_zero]
  | succ k =>
    rw [exactCompactlySupportedForms_succ, exactForms_succ, compactlySupportedForms_eq_top,
      Submodule.map_top]

end CompactSupport

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

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
  have hc {α : SmoothForm I M ℝ l} (hα : α ∈ closedForms I M l) :
      α ∈ compactlySupportedClosedForms I M l :=
    (mem_compactlySupportedClosedForms I).2 ⟨by simp [compactlySupportedForms_eq_top], hα⟩
  have hηc := hc (harmonicForms_le_closedForms o hl1 hη)
  have hcls : compactlySupportedDeRhamCohomology.mk I l ⟨β, hc hβ⟩ =
      compactlySupportedDeRhamCohomology.mk I l ⟨η, hηc⟩ := by
    rw [compactlySupportedDeRhamCohomology.mk_eq_mk_iff,
      exactCompactlySupportedForms_eq_exactForms]
    exact hβη
  have hγη0 : integralTopForm o (RoughForm.wedge (γ : RoughForm I M ℝ 1)
      (η : RoughForm I M ℝ l)) = 0 := by
    have e := poincarePairing_mk o ⟨γ, hγ⟩ ⟨β, hc hβ⟩
    rw [hcls, poincarePairing_mk] at e
    rw [← h γ hγ]
    exact e
  -- Hence `∫ |γ|² vol = 0`, so `γ = 0` and `η = 0`.
  have hnorm := SmoothForm.inner_smul_riemannianVolumeForm_eq_wedge_hodgeStar o rfl γ γ
  have hγ0 : γ = 0 := by
    refine (SmoothForm.integralTopForm_inner_self_smul_riemannianVolumeForm_eq_zero_iff o rfl
      (by simp [compactlySupportedForms_eq_top])).1 ?_
    rw [hnorm, hγη, map_smul, map_smul, Submodule.coe_smul, integralTopForm_smul]
    simpa using hγη0
  have hη0 : η = 0 := by
    have := congrArg ((-1 : ℝ) ^ l • ·) hγη
    simpa [hγ0, smul_smul, ← mul_pow] using this.symm
  simpa [hη0] using hβη

end TauCeti

end
