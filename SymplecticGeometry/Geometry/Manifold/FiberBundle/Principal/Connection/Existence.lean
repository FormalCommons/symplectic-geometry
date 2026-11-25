/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.MaurerCartan
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Connection.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.PartitionOfUnity

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

The proofs adapt those of `SymplecticGeometry.mpullback_op_smul_mpullback_trivialization_snd`,
`SymplecticGeometry.mpullback_trivialization_snd_apply_rightFundamentalVectorField` and
`SymplecticGeometry.exists_isCircleConnectionForm` (the case `G = Circle`, with the angular form
of the circle in place of the Maurer–Cartan form) to a general Lie group.

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
open scoped Manifold ContDiff GroupLieAlgebra

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
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
    MDifferentiableAt (IB.prod IG) IG (fun x : ManifoldTotalSpace G P ↦
      (e ((ManifoldTotalSpace.homeomorph G P).symm x)).2) x)
include hθ

omit [IsManifold IB ∞ B] [ContMDiffFiberBundle ∞ G P IB IG] in
/-- Let `e` be an equivariant trivialization whose fibre coordinate `θ` is differentiable over its
base set. Over the base set, `θ^* θ_MC`, the pull-back of the left Maurer–Cartan form along `θ`, is
equivariant: its pull-back by the action of `g` is its image under `Ad(g⁻¹)`. -/
theorem mpullback_op_smul_mpullback_trivialization_snd_maurerCartan
    {x : ManifoldTotalSpace G P}
    (hx : ((ManifoldTotalSpace.homeomorph G P).symm x).proj ∈ e.baseSet) (g : G) :
    TauCeti.mpullback (IB.prod IG) (IB.prod IG) (fun y : ManifoldTotalSpace G P ↦ op g • y)
      (TauCeti.mpullback (IB.prod IG) IG (fun x : ManifoldTotalSpace G P ↦
        (e ((ManifoldTotalSpace.homeomorph G P).symm x)).2) (leftMaurerCartanForm IG G).val :
          RoughForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1) x =
      RoughForm.mapCoeff (adjointContinuousLinearMap g⁻¹)
        (TauCeti.mpullback (IB.prod IG) IG (fun x : ManifoldTotalSpace G P ↦
          (e ((ManifoldTotalSpace.homeomorph G P).symm x)).2) (leftMaurerCartanForm IG G).val)
        x := by
  set θ := fun x : ManifoldTotalSpace G P ↦ (e ((ManifoldTotalSpace.homeomorph G P).symm x)).2
  have hS := e.open_baseSet.preimage (ManifoldTotalSpace.contMDiff_proj ∞ G P IB IG).continuous
  have hgx : ((ManifoldTotalSpace.homeomorph G P).symm (op g • x)).proj ∈ e.baseSet := by
    simpa [ManifoldTotalSpace.homeomorph_symm_smul] using hx
  have hsmul : MDifferentiableAt (IB.prod IG) (IB.prod IG)
      (fun y : ManifoldTotalSpace G P ↦ op g • y) x :=
    (contMDiff_const_smul (I := IB.prod IG) (n := 1) (op g) x).mdifferentiableAt one_ne_zero
  have hmul : MDifferentiableAt IG IG (fun w : G ↦ w * g) (θ x) :=
    (contMDiff_mul_right (I := IG) (n := 1) (a := g) _).mdifferentiableAt one_ne_zero
  -- Near `x`, the fibre coordinate of `y • g` is that of `y` times `g`.
  have heq : θ ∘ (fun y ↦ op g • y) =ᶠ[nhds x] (fun w : G ↦ w * g) ∘ θ := by
    filter_upwards [hS.mem_nhds hx] with y hy
    simp only [Function.comp_apply, θ, ManifoldTotalSpace.homeomorph_symm_smul]
    exact e.snd_apply_smul hy _ g
  have hR := congrArg Subtype.val (mpullback_mul_right_leftMaurerCartanForm (I := IG) g)
  rw [SmoothForm.coe_mpullback, SmoothForm.coe_mapCoeff] at hR
  rw [← mpullback_comp_at hsmul (hθ _ hgx), heq.mpullback_eq, mpullback_comp_at (hθ _ hx) hmul,
    hR, mpullback_mapCoeff]

omit [IsManifold IB ∞ B] [ContMDiffFiberBundle ∞ G P IB IG] in
/-- Let `e` be an equivariant trivialization whose fibre coordinate `θ` is differentiable over its
base set. Over the base set, `θ^* θ_MC`, the pull-back of the left Maurer–Cartan form along `θ`,
takes the value `ξ` on the fundamental vector field of `ξ`. -/
theorem mpullback_trivialization_snd_maurerCartan_apply_rightFundamentalVectorField
    {x : ManifoldTotalSpace G P}
    (hx : ((ManifoldTotalSpace.homeomorph G P).symm x).proj ∈ e.baseSet)
    (ξ : GroupLieAlgebra IG G) :
    (TauCeti.mpullback (IB.prod IG) IG (fun x : ManifoldTotalSpace G P ↦
        (e ((ManifoldTotalSpace.homeomorph G P).symm x)).2) (leftMaurerCartanForm IG G).val :
          RoughForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1) x
      ![rightFundamentalVectorField (IB.prod IG) ξ x] = ξ := by
  set θ := fun x : ManifoldTotalSpace G P ↦ (e ((ManifoldTotalSpace.homeomorph G P).symm x)).2
  have horb := PrincipalBundle.mdifferentiableAt_orbit (IB := IB) (IG := IG) (n := ∞)
    (by simp) x 1
  have hθx : MDifferentiableAt (IB.prod IG) IG θ (op (1 : G) • x) := by
    rw [op_one, one_smul]
    exact hθ _ hx
  -- Along the orbit of `x`, the fibre coordinate is left multiplication by `θ x`.
  have hcomp : θ ∘ (fun g : G ↦ op g • x) = fun g ↦ θ x * g :=
    funext fun g ↦ by
      simp only [Function.comp_apply, θ, ManifoldTotalSpace.homeomorph_symm_smul]
      exact e.snd_apply_smul hx _ g
  have hv : mfderiv (IB.prod IG) IG θ x (rightFundamentalVectorField (IB.prod IG) ξ x) =
      mulInvariantVectorField ξ (θ x) := by
    rw [GroupLieAlgebra.mulInvariantVectorField_apply, rightFundamentalVectorField_apply, ← hcomp,
      mfderiv_comp_of_eq hθx horb rfl, op_one, one_smul]
    -- `ContinuousLinearMap.comp_apply` does not rewrite here: the inner derivative lands in the
    -- tangent space at `op 1 • x`, which is `x` only after `one_smul`.
    rfl
  have hvec : (fun i ↦ mfderiv (IB.prod IG) IG θ x
      (![rightFundamentalVectorField (IB.prod IG) ξ x] i)) =
      ![mulInvariantVectorField ξ (θ x)] := by
    funext i
    fin_cases i
    exact hv
  rw [mpullback_apply, hvec, leftMaurerCartanForm_apply_mulInvariantVectorField]

end Local

/-! ### Existence -/

/-- **Existence of connection forms.** Every smooth principal `G`-bundle over a Hausdorff,
σ-compact, finite-dimensional base has a connection form. It is glued, with a smooth partition of
unity of the base, from the pull-backs of the left Maurer–Cartan form along the fibre coordinates
of the trivializations of the atlas. -/
theorem exists_isConnectionForm [FiniteDimensional ℝ EB] [T2Space B] [SigmaCompactSpace B] :
    ∃ A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1,
      IsConnectionForm A := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate IB isClosed_univ
    (fun b : B ↦ (trivializationAt G P b).baseSet)
    (fun b ↦ (trivializationAt G P b).open_baseSet)
    (fun b _ ↦ Set.mem_iUnion.2 ⟨b, FiberBundle.mem_baseSet_trivializationAt' b⟩)
  set p := fun x : ManifoldTotalSpace G P ↦
    ((ManifoldTotalSpace.homeomorph G P).symm x).proj with hp
  have hpc : ContMDiff (IB.prod IG) IB ∞ p := ManifoldTotalSpace.contMDiff_proj ∞ G P IB IG
  have hθd (b : B) (x : ManifoldTotalSpace G P) (hx : p x ∈ (trivializationAt G P b).baseSet) :
      ContMDiffAt (IB.prod IG) IG ∞ (fun x : ManifoldTotalSpace G P ↦
        (trivializationAt G P b ((ManifoldTotalSpace.homeomorph G P).symm x)).2) x :=
    (ManifoldTotalSpace.contMDiffOn_trivialization_snd_comp _ (f := fun x ↦ x) contMDiffOn_id
      fun _ hx ↦ hx).contMDiffAt
      (((trivializationAt G P b).open_baseSet.preimage hpc.continuous).mem_nhds hx)
  have hθ (b : B) (x : ManifoldTotalSpace G P) (hx : p x ∈ (trivializationAt G P b).baseSet) :=
    (hθd b x hx).mdifferentiableAt (by simp)
  -- The local connection forms `θ^* θ_MC`, glued with the partition of unity.
  set ℓ : B → RoughForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1 := fun b ↦
    TauCeti.mpullback (IB.prod IG) IG (fun x : ManifoldTotalSpace G P ↦
      (trivializationAt G P b ((ManifoldTotalSpace.homeomorph G P).symm x)).2)
      (leftMaurerCartanForm IG G).val
  set t : B → RoughForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1 :=
    fun b x ↦ ρ b (p x) • ℓ b x with ht
  have hsupp (b : B) (x : ManifoldTotalSpace G P) (hx : t b x ≠ 0) : ρ b (p x) ≠ 0 :=
    left_ne_zero_of_smul hx
  let A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1 :=
    ⟨fun x ↦ ∑ᶠ b, t b x, IsSmoothForm.mem_smoothBundleForms <|
      hρ.isSmoothForm_finsum_smul_comp (fun b ↦ (trivializationAt G P b).open_baseSet) hpc
        fun b x hx ↦ (((SmoothForm.isSmoothForm _).contMDiff _).mpullback_form (hθd b x hx)
          (by simp)).contMDiffWithinAt⟩
  -- Over a point of the base, `A` is a finite sum.
  have hfin (x : ManifoldTotalSpace G P) : ∃ s : Finset B, (∀ b, ρ b (p x) ≠ 0 → b ∈ s) ∧
      ∀ y, p y = p x → A.val y = ∑ b ∈ s, t b y := by
    have h := ρ.locallyFinite.point_finite (p x)
    have hs (b : B) (hb : ρ b (p x) ≠ 0) : b ∈ h.toFinset := by simpa using hb
    exact ⟨h.toFinset, hs, fun y hy ↦ finsum_eq_sum_of_support_subset _ fun b hb ↦
      hs b (hy ▸ hsupp b y hb)⟩
  refine ⟨A, fun g ↦ ?_, fun x ξ ↦ ?_⟩
  · refine Subtype.ext (funext fun x ↦ ?_)
    ext v
    obtain ⟨s, -, hs⟩ := hfin x
    have hpg : p (op g • x) = p x := by simp [hp, ManifoldTotalSpace.homeomorph_symm_smul]
    rw [SmoothForm.coe_mpullback, mpullback_apply, SmoothForm.coe_mapCoeff,
      RoughForm.mapCoeff_apply, hs _ hpg, hs x rfl, ContinuousAlternatingMap.sum_apply,
      ContinuousAlternatingMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    simp only [ht, hpg, ContinuousAlternatingMap.smul_apply, map_smul]
    by_cases hb : ρ b (p x) = 0
    · rw [hb, zero_smul, zero_smul]
    · have hxb : p x ∈ (trivializationAt G P b).baseSet := hρ b (subset_tsupport _ hb)
      congr 1
      have h := DFunLike.congr_fun
        (mpullback_op_smul_mpullback_trivialization_snd_maurerCartan (hθ b) hxb g) v
      rw [mpullback_apply, RoughForm.mapCoeff_apply] at h
      exact h
  · obtain ⟨s, hsmem, hs⟩ := hfin x
    have hterm (b : B) : t b x ![rightFundamentalVectorField (IB.prod IG) ξ x] = ρ b (p x) • ξ := by
      simp only [ht, ContinuousAlternatingMap.smul_apply]
      by_cases hb : ρ b (p x) = 0
      · simp [hb]
      · rw [mpullback_trivialization_snd_maurerCartan_apply_rightFundamentalVectorField
          (hθ b) (hρ b (subset_tsupport _ hb))]
    rw [hs x rfl, ContinuousAlternatingMap.sum_apply, Finset.sum_congr rfl fun b _ ↦ hterm b,
      ← Finset.sum_smul, ← finsum_eq_sum_of_support_subset _ fun b hb ↦ hsmem b hb,
      ρ.sum_eq_one (Set.mem_univ _), one_smul]

end SymplecticGeometry

end
