/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.MaurerCartan
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Connection.Basic
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Trivialization
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.PartitionOfUnity
import TauCeti.Geometry.Manifold.PartitionOfUnity.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Topology.FiberBundle.Basic

/-!
# Existence of connection forms

Let `P` be a smooth principal `G`-bundle over `B`, with charted total space
`TauCeti.ManifoldTotalSpace G P` and Lie algebra `𝔤 = GroupLieAlgebra IG G`. An equivariant
trivialization `e` of `P` gives a fibre coordinate `θ_e x = (e x).2 ∈ G`, with
`θ_e (x • g) = θ_e x * g`. The pull-back `θ_e^* θ_MC` of the left Maurer–Cartan form of `G` is then
a connection form over the base set of `e`: it is equivariant there, because right translation
pulls `θ_MC` back to `Ad(g⁻¹) θ_MC`, and it takes the value `ξ` on the fundamental vector field of
`ξ`, because `θ_e` maps the orbit of `x` to the left translate of `G` by `θ_e x`.

Both conditions of a connection form are affine, so a smooth partition of unity of the base glues
these local forms into a connection form on the whole total space, as soon as the base has one.

## Main results

* `SymplecticGeometry.mpullback_op_smul_mpullback_trivialization_snd_maurerCartan`,
  `SymplecticGeometry.mpullback_trivialization_snd_maurerCartan_apply_rightFundamentalVectorField`:
  over the base set of an equivariant trivialization with fibre coordinate `θ`, `θ^* θ_MC` is
  equivariant and takes the value `ξ` on the fundamental vector field of `ξ`.
* `SymplecticGeometry.exists_isConnectionForm`: every smooth principal bundle over a Hausdorff,
  σ-compact, finite-dimensional base has a connection form.

## Implementation notes

The Maurer–Cartan form is Tau Ceti's `TauCeti.leftMaurerCartanForm`, with values in the model
space `EG`, and its behaviour under right translations is
`TauCeti.leftMaurerCartanForm_apply_mfderiv_mul_right`.

The local lemmas follow from two facts about the fibre coordinate that hold for any form,
`Bundle.Trivialization.mpullback_op_smul_mpullback_snd` and
`Bundle.Trivialization.mfderiv_snd_rightFundamentalVectorField` (`Principal/Trivialization.lean`),
which also give the case `G = Circle`, with the angular form of the circle in place of the
Maurer–Cartan form, in `Principal/CircleConnection.lean`. The circle case of the existence theorem,
`SymplecticGeometry.exists_isCircleConnectionForm`, is derived from `exists_isConnectionForm` in
`Principal/Connection/Circle.lean`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §§1–2 (connection forms of principal bundles and their existence over a paracompact
  base).
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3
  (connection forms on principal bundles).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti TauCeti.Lie
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [LieGroup IG ∞ G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [ContMDiffFiberBundle ∞ G P IB IG]

/-! ### Local connection forms -/

section Local

variable {e : Trivialization G (π G P)} [e.IsEquivariant]

variable (hθ : ∀ x : ManifoldTotalSpace G P,
  ((ManifoldTotalSpace.homeomorph G P).symm x).proj ∈ e.baseSet →
    MDifferentiableAt (IB.prod IG) IG e.manifoldSnd x)
include hθ

omit [IsManifold IB ∞ B] [ContMDiffFiberBundle ∞ G P IB IG] in
/-- Let `e` be an equivariant trivialization whose fibre coordinate `θ` is differentiable over its
base set. Over the base set, `θ^* θ_MC`, the pull-back of the left Maurer–Cartan form along `θ`, is
equivariant: its pull-back by the action of `g` is its image under `Ad(g⁻¹)`. -/
theorem mpullback_op_smul_mpullback_trivialization_snd_maurerCartan
    {x : ManifoldTotalSpace G P}
    (hx : ((ManifoldTotalSpace.homeomorph G P).symm x).proj ∈ e.baseSet) (g : G) :
    TauCeti.mpullback (IB.prod IG) (IB.prod IG) (fun y : ManifoldTotalSpace G P ↦ op g • y)
      (TauCeti.mpullback (IB.prod IG) IG e.manifoldSnd (leftMaurerCartanForm IG G).val) x =
      RoughForm.mapCoeff (GroupLieAlgebra.adjointL IG g⁻¹)
        (TauCeti.mpullback (IB.prod IG) IG e.manifoldSnd (leftMaurerCartanForm IG G).val) x := by
  rw [e.mpullback_op_smul_mpullback_snd hθ hx]
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, funext fun i ↦ by rw [Subsingleton.elim i 0]; rfl⟩
  rw [RoughForm.mapCoeff_apply, mpullback_apply_one, mpullback_apply_one, mpullback_apply_one,
    leftMaurerCartanForm_apply_mfderiv_mul_right, GroupLieAlgebra.adjointL_apply]

omit [IsManifold IB ∞ B] [ContMDiffFiberBundle ∞ G P IB IG] in
/-- Let `e` be an equivariant trivialization whose fibre coordinate `θ` is differentiable over its
base set. Over the base set, `θ^* θ_MC`, the pull-back of the left Maurer–Cartan form along `θ`,
takes the value `ξ` on the fundamental vector field of `ξ`. -/
theorem mpullback_trivialization_snd_maurerCartan_apply_rightFundamentalVectorField
    {x : ManifoldTotalSpace G P}
    (hx : ((ManifoldTotalSpace.homeomorph G P).symm x).proj ∈ e.baseSet)
    (ξ : GroupLieAlgebra IG G) :
    (TauCeti.mpullback (IB.prod IG) IG e.manifoldSnd (leftMaurerCartanForm IG G).val :
        RoughForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1) x
      ![rightFundamentalVectorField (IB.prod IG) ξ x] = ξ := by
  rw [mpullback_apply_one, e.mfderiv_snd_rightFundamentalVectorField hx (hθ _ hx) ξ,
    leftMaurerCartanForm_apply_mulInvariantVectorField]

end Local

/-! ### Existence -/

/-- **Existence of connection forms.** Every smooth principal `G`-bundle over a Hausdorff,
σ-compact, finite-dimensional base has a connection form. It is glued, with a smooth partition of
unity of the base, from the pull-backs of the left Maurer–Cartan form along the fibre coordinates
of the trivializations of the atlas. -/
theorem exists_isConnectionForm [FiniteDimensional ℝ EB] [T2Space B] [SigmaCompactSpace B] :
    ∃ A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1,
      IsConnectionForm A := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate IB isClosed_univ
    (fun b : B ↦ (trivializationAt G P b).baseSet)
    (fun b ↦ (trivializationAt G P b).open_baseSet)
    (FiberBundle.iUnion_baseSet_trivializationAt G P).ge
  set p := ManifoldTotalSpace.projContMDiffMap ∞ G P IB IG with hp
  have hpc : ContMDiff (IB.prod IG) IB ∞ p := p.contMDiff
  have hθd (b : B) (x : ManifoldTotalSpace G P) (hx : p x ∈ (trivializationAt G P b).baseSet) :
      ContMDiffAt (IB.prod IG) IG ∞ (trivializationAt G P b).manifoldSnd x :=
    ((trivializationAt G P b).contMDiffOn_manifoldSnd (IB := IB)).contMDiffAt
      (((trivializationAt G P b).open_baseSet.preimage hpc.continuous).mem_nhds hx)
  have hθ (b : B) (x : ManifoldTotalSpace G P) (hx : p x ∈ (trivializationAt G P b).baseSet) :=
    (hθd b x hx).mdifferentiableAt (by simp)
  -- The local connection forms `θ^* θ_MC`, glued with the partition of unity.
  set ℓ : B → RoughForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1 := fun b ↦
    TauCeti.mpullback (IB.prod IG) IG (trivializationAt G P b).manifoldSnd
      (leftMaurerCartanForm IG G).val
  let A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1 :=
    ⟨fun x ↦ ∑ b ∈ ρ.finsupport (p x), ρ b (p x) • ℓ b x, IsSmoothForm.mem_smoothBundleForms <|
      isSmoothForm_sum_finsupport_smul_mpullback hρ
        (fun b ↦ (trivializationAt G P b).open_baseSet) hpc hθd (leftMaurerCartanForm IG G)⟩
  have hA (x : ManifoldTotalSpace G P) (v : Fin 1 → TangentSpace (IB.prod IG) x) :
      A.val x v = ∑ b ∈ ρ.finsupport (p x), ρ b (p x) • ℓ b x v := by
    simp only [A, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply]
  refine ⟨A, fun g ↦ ?_, fun x ξ ↦ ?_⟩
  · refine SmoothBundleForm.ext fun x v ↦ ?_
    have hpg : p (op g • x) = p x := by simp [hp, ManifoldTotalSpace.homeomorph_symm_smul]
    rw [SmoothForm.coe_mpullback, mpullback_apply, SmoothForm.coe_mapCoeff,
      RoughForm.mapCoeff_apply, hA, hA, map_sum, hpg]
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    have h := DFunLike.congr_fun (mpullback_op_smul_mpullback_trivialization_snd_maurerCartan
      (hθ b) (hρ.mem_of_mem_finsupport hb) g) v
    rw [mpullback_apply, RoughForm.mapCoeff_apply] at h
    rw [map_smul, ← h]
  · rw [hA]
    exact ρ.sum_finsupport_smul_eq_of_forall_eq (Set.mem_univ _)
      fun b hb ↦ mpullback_trivialization_snd_maurerCartan_apply_rightFundamentalVectorField
        (hθ b) (hρ.mem_of_mem_finsupport hb) ξ

end SymplecticGeometry

end
