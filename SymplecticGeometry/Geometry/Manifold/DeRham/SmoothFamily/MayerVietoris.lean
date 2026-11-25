/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Projection
public import SymplecticGeometry.Geometry.Manifold.DeRham.SmoothFamily.Basic
public import SymplecticGeometry.Geometry.Manifold.DeRham.SmoothFamily.Cutoff
import SymplecticGeometry.Geometry.Manifold.DeRham.Map

/-!
# The Mayer–Vietoris step for smooth cohomology splittings

Let `U` and `V` be open sets of a Hausdorff σ-compact manifold modelled on a finite-dimensional
space. If `U`, `V` and `U ⊓ V` have smooth cohomology splittings
(`SymplecticGeometry.SmoothCohomologySplitting` with
`SymplecticGeometry.SmoothCohomologySplitting.IsSmooth`), then so does `U ⊔ V`
(`SymplecticGeometry.SmoothCohomologySplitting.exists_isSmooth_sup`). This is the inductive
step of the induction over a finite good cover that McDuff and Salamon sketch, after Bott and Tu,
in the proof of their Theorem 3.2.4 [McDuffSalamon2017], [BottTu1982].

The splitting `SmoothCohomologySplitting.sup c σU σV σUV` is built from splittings `σU`, `σV`,
`σUV` of `U`, `V`, `U ⊓ V` and a cut-off function `c` (`ρ` below,
`SymplecticGeometry.MayerVietorisCutoff`). In degree zero its space is the space of all closed
`0`-forms, finite-dimensional because restriction embeds it into the closed `0`-forms on `U` and
on `V`. In degree `k + 1`, for a closed form `z` on `U ⊔ V`:

1. The pair of projections of the restrictions of `z` to `U` and to `V` lies in the
   finite-dimensional space `exactPairs` of pairs of forms of the two spaces whose difference on
   `U ⊓ V` is exact. Every such pair comes from a closed form on `U ⊔ V`
   (`MayerVietorisCutoff.exists_projPair_eq`), and a fixed linear right inverse
   `MayerVietorisCutoff.liftPair` gives a closed form `g` with the same pair. Then `z - g`
   (`MayerVietorisCutoff.exactOnPieces`) is exact on `U` and on `V`, with primitives `a` and `b`
   given by the primitives of `σU` and `σV`.
2. The closed `k`-form `a - b` on `U ⊓ V` (`MayerVietorisCutoff.discrepancy`) has a projection
   under `σUV`, which splits into a component in the range `R` of the projections of differences
   of closed forms on `U` and on `V`, and a component `q` in a fixed complement of `R`. Through a
   fixed linear right inverse `overlapLift`, the first component is the projection of the
   difference of closed forms `x` on `U` and `y` on `V`; replacing `a` and `b` by `a - x` and
   `b - y` gives a discrepancy whose projection is `q`
   (`MayerVietorisCutoff.proj_correctedDiscrepancy`).
3. The forms `a - x - d (ρ w) - ρ q` on `U` and `b - y + d ((1 - ρ) w) + (1 - ρ) q` on `V`, with
   `w` the primitive under `σUV` of the corrected discrepancy (and `d w` read as `0` in degree
   zero), agree on `U ⊓ V` and glue to the new primitive `MayerVietorisCutoff.supPrimitive`. Its
   exterior derivative is `z` minus the new projection `g + δ q`
   (`MayerVietorisCutoff.supProj`), where `δ` is the connecting form of
   `MayerVietorisCutoff.connecting`.
4. The new space, spanned by the forms `g` and the connecting forms of the complement
   (`MayerVietorisCutoff.supSpace`), contains no nonzero exact form
   (`MayerVietorisCutoff.eq_zero_of_mem_supSpace`).

Every map is assembled from restrictions, cut-off and extension by zero, the exterior derivative,
gluing, the maps of the three splittings, and linear maps out of finite-dimensional spaces whose
arguments have smooth coordinates along smooth families; so the new projection and primitive take
smooth families to smooth families when those of the three splittings do
(`MayerVietorisCutoff.preservesSmoothFamilies_supProj`,
`MayerVietorisCutoff.preservesSmoothFamilies_supPrimitive`,
`SmoothCohomologySplitting.IsSmooth.sup`). The construction itself makes no reference to
smoothness, so `sup` does not depend on the universes of parameter manifolds. Where the sketch
fixes bases and forms attached to them, the construction here takes linear right inverses of
surjective linear maps onto finite-dimensional spaces.

## Main definitions

* `SymplecticGeometry.SmoothCohomologySplitting.sup`: the splitting of `U ⊔ V`.

## Main results

* `SymplecticGeometry.SmoothCohomologySplitting.IsSmooth.sup`: `sup` of smooth splittings is
  smooth.
* `SymplecticGeometry.SmoothCohomologySplitting.exists_isSmooth_sup`: smooth splittings of `U`,
  `V` and `U ⊓ V` give one of `U ⊔ V`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], proof of
  Theorem 3.2.4.
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §§2 and 5.
-/

public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold Topology ContDiff

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ} {U V : Opens M}

universe uE uH uN

namespace SymplecticGeometry

open TauCeti

section OverlapDiff

variable [IsManifold I ∞ M]

/-- The difference on `U ⊓ V` of closed forms on `U` and on `V`, a closed form. -/
def overlapDiff (k : ℕ) :
    closedForms I U k × closedForms I V k →ₗ[ℝ] closedForms I (U ⊓ V : Opens M) k :=
  (SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _) ∘ₗ
      (closedForms I U k).subtype ∘ₗ LinearMap.fst _ _ _ -
    SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _) ∘ₗ
      (closedForms I V k).subtype ∘ₗ LinearMap.snd _ _ _).codRestrict _ fun p ↦ by
    rw [LinearMap.sub_apply]
    exact sub_mem (SmoothForm.mpullback_mem_closedForms _ _ p.1.property)
      (SmoothForm.mpullback_mem_closedForms _ _ p.2.property)

/-- The underlying form of `overlapDiff`. -/
theorem coe_overlapDiff (k : ℕ) (p : closedForms I U k × closedForms I V k) :
    (overlapDiff k p : SmoothForm I (U ⊓ V : Opens M) ℝ k) =
      SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _)
          (p.1 : SmoothForm I U ℝ k) -
        SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _)
          (p.2 : SmoothForm I V ℝ k) :=
  (rfl)

end OverlapDiff

namespace SmoothCohomologySplitting

variable [IsManifold I ∞ M] (σU : SmoothCohomologySplitting I U)
  (σV : SmoothCohomologySplitting I V) (σUV : SmoothCohomologySplitting I (U ⊓ V : Opens M))

/-! ### Step 1: pairs of representatives with exact difference -/

/-- The pairs `(x, y)` of forms of the spaces of splittings on `U` and on `V` whose difference on
`U ⊓ V` is exact. -/
def exactPairs (n : ℕ) : Submodule ℝ (SmoothForm I U ℝ n × SmoothForm I V ℝ n) :=
  (σU.space n).prod (σV.space n) ⊓ (exactForms I (U ⊓ V : Opens M) n).comap
    ((SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _)).coprod
      (-SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _)))

/-- Membership in `exactPairs`. -/
theorem mem_exactPairs_iff {n : ℕ} {p : SmoothForm I U ℝ n × SmoothForm I V ℝ n} :
    p ∈ σU.exactPairs σV n ↔ p.1 ∈ σU.space n ∧ p.2 ∈ σV.space n ∧
      SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _) p.1 -
        SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _) p.2 ∈
          exactForms I (U ⊓ V : Opens M) n := by
  simp [exactPairs, sub_eq_add_neg, and_assoc]

instance finiteDimensional_exactPairs (n : ℕ) : FiniteDimensional ℝ (σU.exactPairs σV n) :=
  have := isNoetherian_of_isNoetherianRing_of_finite ℝ (σU.space n)
  have := isNoetherian_of_isNoetherianRing_of_finite ℝ (σV.space n)
  have := isNoetherian_prod (R := ℝ) (M := σU.space n) (N := σV.space n)
  Module.Finite.of_injective
    ((LinearMap.fst _ _ _ ∘ₗ (σU.exactPairs σV n).subtype).codRestrict (σU.space n)
        (fun p ↦ ((σU.mem_exactPairs_iff σV).mp p.property).1) |>.prod
      ((LinearMap.snd _ _ _ ∘ₗ (σU.exactPairs σV n).subtype).codRestrict (σV.space n)
        (fun p ↦ ((σU.mem_exactPairs_iff σV).mp p.property).2.1)))
    fun p q h ↦ by
      have h₁ := congrArg (fun x : σU.space n × σV.space n ↦ (x.1 : SmoothForm I U ℝ n)) h
      have h₂ := congrArg (fun x : σU.space n × σV.space n ↦ (x.2 : SmoothForm I V ℝ n)) h
      exact Subtype.ext (Prod.ext h₁ h₂)

/-- The projections of the restrictions to `U` and to `V` of a closed form on `U ⊔ V`. -/
def projPair (n : ℕ) :
    closedForms I (U ⊔ V : Opens M) n →ₗ[ℝ] SmoothForm I U ℝ n × SmoothForm I V ℝ n :=
  (σU.proj n ∘ₗ
      closedForms.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) n).prod
    (σV.proj n ∘ₗ
      closedForms.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) n)

/-- The components of `projPair`. -/
@[simp]
theorem projPair_apply {n : ℕ} (z : closedForms I (U ⊔ V : Opens M) n) :
    σU.projPair σV n z =
      (σU.proj n
          (closedForms.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) n z),
        σV.proj n
          (closedForms.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) n z)) :=
  (rfl)

/-- The projections of the restrictions of a closed `(k + 1)`-form on `U ⊔ V` have exact
difference on `U ⊓ V`. -/
theorem projPair_mem_exactPairs (z : closedForms I (U ⊔ V : Opens M) (k + 1)) :
    σU.projPair σV (k + 1) z ∈ σU.exactPairs σV (k + 1) := by
  refine (σU.mem_exactPairs_iff σV).mpr ⟨σU.proj_mem _ _, σV.proj_mem _ _, ?_⟩
  rw [projPair_apply, proj_eq_sub_mextDerivₗ_primitive, proj_eq_sub_mextDerivₗ_primitive,
    exactForms_succ]
  refine ⟨SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _)
      (σV.primitive k
        (closedForms.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) _ z)) -
    SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _)
      (σU.primitive k
        (closedForms.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) _ z)), ?_⟩
  simp only [map_sub, SmoothForm.mextDerivₗ_mpullback, closedForms.coe_mpullback,
    SmoothForm.mpullback_inclusion_inf_sup_left_eq_right]
  abel

/-- `projPair`, with its values in `exactPairs`. -/
def projExactPair (k : ℕ) :
    closedForms I (U ⊔ V : Opens M) (k + 1) →ₗ[ℝ] σU.exactPairs σV (k + 1) :=
  (σU.projPair σV (k + 1)).codRestrict _ (σU.projPair_mem_exactPairs σV)

/-- The underlying pair of `projExactPair`. -/
@[simp]
theorem coe_projExactPair (z : closedForms I (U ⊔ V : Opens M) (k + 1)) :
    (σU.projExactPair σV k z : SmoothForm I U ℝ (k + 1) × SmoothForm I V ℝ (k + 1)) =
      σU.projPair σV (k + 1) z :=
  (rfl)

/-! ### Step 2: the projections on `U ⊓ V` of differences, and a complement -/

/-- The projection on `U ⊓ V` of the difference of closed forms on `U` and on `V`. -/
def overlapProj (k : ℕ) :
    closedForms I U k × closedForms I V k →ₗ[ℝ] SmoothForm I (U ⊓ V : Opens M) ℝ k :=
  σUV.proj k ∘ₗ overlapDiff k

/-- `overlapProj` is the projection of `overlapDiff`. -/
theorem overlapProj_apply (k : ℕ) (p : closedForms I U k × closedForms I V k) :
    σUV.overlapProj k p = σUV.proj k (overlapDiff k p) :=
  (rfl)

/-- The values of `overlapProj` lie in the space of the splitting of `U ⊓ V`. -/
theorem range_overlapProj_le (k : ℕ) : LinearMap.range (σUV.overlapProj k) ≤ σUV.space k := by
  rintro _ ⟨p, rfl⟩
  exact σUV.proj_mem _ _

/-- A fixed complement of the range of `overlapProj`. -/
def overlapCompl (k : ℕ) : Submodule ℝ (SmoothForm I (U ⊓ V : Opens M) ℝ k) :=
  (Submodule.exists_isCompl (LinearMap.range (σUV.overlapProj k))).choose

/-- `overlapCompl` is a complement of the range of `overlapProj`. -/
theorem isCompl_overlapCompl (k : ℕ) :
    IsCompl (LinearMap.range (σUV.overlapProj k)) (σUV.overlapCompl k) :=
  (Submodule.exists_isCompl (LinearMap.range (σUV.overlapProj k))).choose_spec

private theorem exists_overlapLift (k : ℕ) :
    ∃ g : LinearMap.range (σUV.overlapProj k) →ₗ[ℝ] closedForms I U k × closedForms I V k,
      (σUV.overlapProj k).rangeRestrict ∘ₗ g = LinearMap.id :=
  have := Module.Free.of_divisionRing ℝ (LinearMap.range (σUV.overlapProj k))
  (σUV.overlapProj k).rangeRestrict.exists_rightInverse_of_surjective
    (σUV.overlapProj k).range_rangeRestrict

/-- A fixed linear right inverse of `overlapProj` on its range. -/
def overlapLift (k : ℕ) :
    LinearMap.range (σUV.overlapProj k) →ₗ[ℝ] closedForms I U k × closedForms I V k :=
  (exists_overlapLift σUV k).choose

/-- `overlapLift` is a right inverse of `overlapProj`. -/
@[simp]
theorem overlapProj_overlapLift (k : ℕ) (r : LinearMap.range (σUV.overlapProj k)) :
    σUV.overlapProj k (σUV.overlapLift k r) = r :=
  congrArg Subtype.val (LinearMap.congr_fun (exists_overlapLift σUV k).choose_spec r)

/-- The component in the range of `overlapProj` of a form of the space of the splitting. -/
def rangeProj (k : ℕ) : σUV.space k →ₗ[ℝ] LinearMap.range (σUV.overlapProj k) :=
  Submodule.projectionOnto _ _ (σUV.isCompl_overlapCompl k) ∘ₗ (σUV.space k).subtype

/-- The component in the fixed complement of a form of the space of the splitting lies in that
space. -/
theorem projectionOnto_overlapCompl_mem_inf (k : ℕ) (s : σUV.space k) :
    (Submodule.projectionOnto _ _ (σUV.isCompl_overlapCompl k).symm s :
        SmoothForm I (U ⊓ V : Opens M) ℝ k) ∈ σUV.overlapCompl k ⊓ σUV.space k := by
  refine ⟨Submodule.coe_mem _, ?_⟩
  have h := Submodule.projection_add_projection_eq_self (σUV.isCompl_overlapCompl k) s
  rw [← eq_sub_iff_add_eq'] at h
  rw [Submodule.coe_projectionOnto_apply, h]
  exact sub_mem s.property (σUV.range_overlapProj_le k (Submodule.projection_apply_mem _ _))

/-- The component in the fixed complement of a form of the space of the splitting, which lies in
that space. -/
def complProj (k : ℕ) : σUV.space k →ₗ[ℝ] (σUV.overlapCompl k ⊓ σUV.space k : Submodule ℝ _) :=
  (Submodule.subtype _ ∘ₗ Submodule.projectionOnto _ _ (σUV.isCompl_overlapCompl k).symm ∘ₗ
    (σUV.space k).subtype).codRestrict _ (σUV.projectionOnto_overlapCompl_mem_inf k)

/-- A form of the space of the splitting is the sum of its two components. -/
theorem coe_rangeProj_add_coe_complProj (k : ℕ) (s : σUV.space k) :
    ((σUV.rangeProj k s : LinearMap.range (σUV.overlapProj k)) :
        SmoothForm I (U ⊓ V : Opens M) ℝ k) +
      (σUV.complProj k s : SmoothForm I (U ⊓ V : Opens M) ℝ k) = s :=
  Submodule.projection_add_projection_eq_self (σUV.isCompl_overlapCompl k) s

/-- The forms of the fixed complement that lie in the space of the splitting are closed. -/
theorem overlapCompl_inf_space_le_closedForms (k : ℕ) :
    σUV.overlapCompl k ⊓ σUV.space k ≤ closedForms I (U ⊓ V : Opens M) k :=
  inf_le_right.trans (σUV.space_le_closedForms k)

end SmoothCohomologySplitting

namespace MayerVietorisCutoff

variable [IsManifold I ∞ M] (c : MayerVietorisCutoff I U V) (σU : SmoothCohomologySplitting I U)
  (σV : SmoothCohomologySplitting I V) (σUV : SmoothCohomologySplitting I (U ⊓ V : Opens M))

include c in
/-- Every pair of `exactPairs` in positive degree is the pair of projections of the restrictions
of a closed form on `U ⊔ V`: if `x - y = d w` on `U ⊓ V`, the forms `x - d (ρ w)` on `U` and
`y + d ((1 - ρ) w)` on `V` glue to one. -/
theorem exists_projPair_eq {p : SmoothForm I U ℝ (k + 1) × SmoothForm I V ℝ (k + 1)}
    (hp : p ∈ σU.exactPairs σV (k + 1)) :
    ∃ g : closedForms I (U ⊔ V : Opens M) (k + 1), σU.projPair σV (k + 1) g = p := by
  obtain ⟨hp₁, hp₂, hex⟩ := (σU.mem_exactPairs_iff σV).mp hp
  rw [exactForms_succ] at hex
  obtain ⟨w, hw⟩ := hex
  have hsum := c.mpullback_mextDerivₗ_extendLeft_add_mpullback_mextDerivₗ_extendRight w
  have hagree : SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _)
      (p.1 - mextDerivₗ I k (c.extendLeft w)) =
      SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _)
      (p.2 + mextDerivₗ I k (c.extendRight w)) := by
    rw [map_sub, map_add, eq_sub_of_add_eq' hsum, hw]
    abel
  obtain ⟨g, hg⟩ := (SmoothForm.exact_mayerVietoris (I := I) (F := ℝ) (k := k + 1) U V
    (_, _)).mp (by
      rw [LinearMap.coprod_apply, LinearMap.neg_apply, hagree, add_neg_cancel])
  simp only [LinearMap.prod_apply, Function.prod_apply, Prod.mk.injEq] at hg
  have hc₁ := σU.space_le_closedForms _ hp₁
  have hc₂ := σV.space_le_closedForms _ hp₂
  rw [mem_closedForms_iff_mextDerivₗ_eq_zero] at hc₁ hc₂
  have hgc : g ∈ closedForms I (U ⊔ V : Opens M) (k + 1) := by
    rw [mem_closedForms_iff_mextDerivₗ_eq_zero]
    refine SmoothForm.injective_mayerVietoris U V ?_
    simp only [map_zero, LinearMap.prod_apply, Function.prod_apply,
      ← SmoothForm.mextDerivₗ_mpullback,
      hg.1, hg.2, map_sub, map_add, hc₁, hc₂, zero_sub, zero_add, neg_eq_zero, Prod.mk_eq_zero]
    exact ⟨LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I k) _,
      LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I k) _⟩
  refine ⟨⟨g, hgc⟩, Prod.ext (σU.proj_eq_of_sub_mem_exactForms hp₁ ?_)
    (σV.proj_eq_of_sub_mem_exactForms hp₂ ?_)⟩
  · rw [closedForms.coe_mpullback, hg.1, sub_sub_cancel_left, exactForms_succ, ← map_neg]
    exact LinearMap.mem_range_self _ _
  · rw [closedForms.coe_mpullback, hg.2, add_sub_cancel_left, exactForms_succ]
    exact LinearMap.mem_range_self _ _

include c in
private theorem exists_liftPair (k : ℕ) :
    ∃ g : σU.exactPairs σV (k + 1) →ₗ[ℝ] closedForms I (U ⊔ V : Opens M) (k + 1),
      σU.projExactPair σV k ∘ₗ g = LinearMap.id :=
  have := Module.Free.of_divisionRing ℝ (σU.exactPairs σV (k + 1))
  (σU.projExactPair σV k).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr fun p ↦ (c.exists_projPair_eq σU σV p.property).imp
      fun _ h ↦ Subtype.ext h)

/-- A fixed linear right inverse of `projExactPair`: closed forms on `U ⊔ V` with prescribed
projections of their restrictions to `U` and to `V`. -/
def liftPair (k : ℕ) :
    σU.exactPairs σV (k + 1) →ₗ[ℝ] closedForms I (U ⊔ V : Opens M) (k + 1) :=
  (c.exists_liftPair σU σV k).choose

/-- `liftPair` is a right inverse of `projExactPair`. -/
@[simp]
theorem projExactPair_liftPair (p : σU.exactPairs σV (k + 1)) :
    σU.projExactPair σV k (c.liftPair σU σV k p) = p :=
  LinearMap.congr_fun (c.exists_liftPair σU σV k).choose_spec p

/-- Step 1: a closed form on `U ⊔ V`, corrected by a fixed closed form so that the projections of
its restrictions to `U` and to `V` vanish. -/
def exactOnPieces (k : ℕ) :
    closedForms I (U ⊔ V : Opens M) (k + 1) →ₗ[ℝ] closedForms I (U ⊔ V : Opens M) (k + 1) :=
  ((closedForms I _ _).subtype -
    (closedForms I _ _).subtype ∘ₗ c.liftPair σU σV k ∘ₗ σU.projExactPair σV k).codRestrict _
      fun z ↦ sub_mem z.property (Submodule.coe_mem _)

/-- The underlying form of `exactOnPieces`. -/
theorem coe_exactOnPieces (z : closedForms I (U ⊔ V : Opens M) (k + 1)) :
    (c.exactOnPieces σU σV k z : SmoothForm I (U ⊔ V : Opens M) ℝ (k + 1)) =
      z - c.liftPair σU σV k (σU.projExactPair σV k z) :=
  (rfl)

/-- The projections of the restrictions of `exactOnPieces z` to `U` and to `V` vanish. -/
theorem projPair_exactOnPieces (z : closedForms I (U ⊔ V : Opens M) (k + 1)) :
    σU.projPair σV (k + 1) (c.exactOnPieces σU σV k z) = 0 := by
  have h := congrArg Subtype.val (c.projExactPair_liftPair σU σV (σU.projExactPair σV k z))
  rw [SmoothCohomologySplitting.coe_projExactPair, SmoothCohomologySplitting.coe_projExactPair,
    SmoothCohomologySplitting.projPair_apply, SmoothCohomologySplitting.projPair_apply,
    Prod.mk.injEq] at h
  rw [SmoothCohomologySplitting.projPair_apply, Prod.mk_eq_zero, σU.proj_eq_zero_iff,
    σV.proj_eq_zero_iff, closedForms.coe_mpullback, closedForms.coe_mpullback, coe_exactOnPieces,
    map_sub, map_sub]
  constructor
  · simpa only [h.1, sub_sub_sub_cancel_right, closedForms.coe_mpullback] using
      sub_mem (σU.sub_proj_mem_exactForms
          (closedForms.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) _ z))
        (σU.sub_proj_mem_exactForms
          (closedForms.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) _
            (c.liftPair σU σV k (σU.projExactPair σV k z))))
  · simpa only [h.2, sub_sub_sub_cancel_right, closedForms.coe_mpullback] using
      sub_mem (σV.sub_proj_mem_exactForms
          (closedForms.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) _ z))
        (σV.sub_proj_mem_exactForms
          (closedForms.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) _
            (c.liftPair σU σV k (σU.projExactPair σV k z))))

/-- The primitive on `U` of the restriction of `exactOnPieces`. -/
def primitiveLeft (k : ℕ) :
    closedForms I (U ⊔ V : Opens M) (k + 1) →ₗ[ℝ] SmoothForm I U ℝ k :=
  σU.primitive k ∘ₗ
    closedForms.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) (k + 1) ∘ₗ
      c.exactOnPieces σU σV k

/-- The primitive on `V` of the restriction of `exactOnPieces`. -/
def primitiveRight (k : ℕ) :
    closedForms I (U ⊔ V : Opens M) (k + 1) →ₗ[ℝ] SmoothForm I V ℝ k :=
  σV.primitive k ∘ₗ
    closedForms.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) (k + 1) ∘ₗ
      c.exactOnPieces σU σV k

/-- `primitiveLeft z` is a primitive of the restriction of `exactOnPieces z` to `U`. -/
theorem mextDerivₗ_primitiveLeft (z : closedForms I (U ⊔ V : Opens M) (k + 1)) :
    mextDerivₗ I k (c.primitiveLeft σU σV k z) =
      SmoothForm.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _)
        (c.exactOnPieces σU σV k z : SmoothForm I (U ⊔ V : Opens M) ℝ (k + 1)) := by
  have h : σU.proj (k + 1) (closedForms.mpullback (Opens.inclusion le_sup_left)
      (contMDiff_inclusion _) (k + 1) (c.exactOnPieces σU σV k z)) = 0 :=
    congrArg Prod.fst (c.projPair_exactOnPieces σU σV z)
  rw [primitiveLeft, LinearMap.comp_apply, LinearMap.comp_apply, σU.mextDerivₗ_primitive, h,
    sub_zero, closedForms.coe_mpullback]

/-- `primitiveRight z` is a primitive of the restriction of `exactOnPieces z` to `V`. -/
theorem mextDerivₗ_primitiveRight (z : closedForms I (U ⊔ V : Opens M) (k + 1)) :
    mextDerivₗ I k (c.primitiveRight σU σV k z) =
      SmoothForm.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _)
        (c.exactOnPieces σU σV k z : SmoothForm I (U ⊔ V : Opens M) ℝ (k + 1)) := by
  have h : σV.proj (k + 1) (closedForms.mpullback (Opens.inclusion le_sup_right)
      (contMDiff_inclusion _) (k + 1) (c.exactOnPieces σU σV k z)) = 0 :=
    congrArg Prod.snd (c.projPair_exactOnPieces σU σV z)
  rw [primitiveRight, LinearMap.comp_apply, LinearMap.comp_apply, σV.mextDerivₗ_primitive, h,
    sub_zero, closedForms.coe_mpullback]

/-- The discrepancy on `U ⊓ V` of the two primitives, a closed `k`-form. -/
def discrepancy (k : ℕ) :
    closedForms I (U ⊔ V : Opens M) (k + 1) →ₗ[ℝ] closedForms I (U ⊓ V : Opens M) k :=
  (SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _) ∘ₗ
      c.primitiveLeft σU σV k -
    SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _) ∘ₗ
      c.primitiveRight σU σV k).codRestrict _ fun z ↦ by
    rw [mem_closedForms_iff_mextDerivₗ_eq_zero, LinearMap.sub_apply, map_sub,
      LinearMap.comp_apply, LinearMap.comp_apply, SmoothForm.mextDerivₗ_mpullback,
      SmoothForm.mextDerivₗ_mpullback, mextDerivₗ_primitiveLeft, mextDerivₗ_primitiveRight,
      SmoothForm.mpullback_inclusion_inf_sup_left_eq_right, sub_self]

/-- The underlying form of `discrepancy`. -/
theorem coe_discrepancy (z : closedForms I (U ⊔ V : Opens M) (k + 1)) :
    (c.discrepancy σU σV k z : SmoothForm I (U ⊓ V : Opens M) ℝ k) =
      SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _)
          (c.primitiveLeft σU σV k z) -
        SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _)
          (c.primitiveRight σU σV k z) :=
  (rfl)

/-- Step 2: the component in the range of `overlapProj` of the projection of the
discrepancy. -/
def rangePart (k : ℕ) :
    closedForms I (U ⊔ V : Opens M) (k + 1) →ₗ[ℝ] LinearMap.range (σUV.overlapProj k) :=
  σUV.rangeProj k ∘ₗ σUV.projSpace k ∘ₗ c.discrepancy σU σV k

/-- Step 2: the component in the fixed complement of the projection of the discrepancy. -/
def complementPart (k : ℕ) : closedForms I (U ⊔ V : Opens M) (k + 1) →ₗ[ℝ]
    (σUV.overlapCompl k ⊓ σUV.space k : Submodule ℝ _) :=
  σUV.complProj k ∘ₗ σUV.projSpace k ∘ₗ c.discrepancy σU σV k

/-- Step 2: the discrepancy, corrected by the difference on `U ⊓ V` of fixed closed forms on `U`
and on `V`, so that its projection lies in the fixed complement. -/
def correctedDiscrepancy (k : ℕ) :
    closedForms I (U ⊔ V : Opens M) (k + 1) →ₗ[ℝ] closedForms I (U ⊓ V : Opens M) k :=
  ((closedForms I _ _).subtype ∘ₗ c.discrepancy σU σV k -
    (closedForms I _ _).subtype ∘ₗ overlapDiff k ∘ₗ σUV.overlapLift k ∘ₗ
      c.rangePart σU σV σUV k).codRestrict _
    fun _ ↦ sub_mem (Submodule.coe_mem _) (Submodule.coe_mem _)

/-- The underlying form of `correctedDiscrepancy`. -/
theorem coe_correctedDiscrepancy (z : closedForms I (U ⊔ V : Opens M) (k + 1)) :
    (c.correctedDiscrepancy σU σV σUV k z : SmoothForm I (U ⊓ V : Opens M) ℝ k) =
      (c.discrepancy σU σV k z : SmoothForm I (U ⊓ V : Opens M) ℝ k) -
        overlapDiff k (σUV.overlapLift k (c.rangePart σU σV σUV k z)) :=
  (rfl)

/-- The component in the fixed complement lies in the space of the splitting of `U ⊓ V`. -/
theorem coe_complementPart_mem_space (z : closedForms I (U ⊔ V : Opens M) (k + 1)) :
    (c.complementPart σU σV σUV k z : SmoothForm I (U ⊓ V : Opens M) ℝ k) ∈ σUV.space k :=
  (c.complementPart σU σV σUV k z).property.2

/-- The projection of the corrected discrepancy is the component of step 2 in the fixed
complement. -/
theorem proj_correctedDiscrepancy (z : closedForms I (U ⊔ V : Opens M) (k + 1)) :
    σUV.proj k (c.correctedDiscrepancy σU σV σUV k z) =
      (c.complementPart σU σV σUV k z : SmoothForm I (U ⊓ V : Opens M) ℝ k) := by
  refine σUV.proj_eq_of_sub_mem_exactForms (c.coe_complementPart_mem_space σU σV σUV z) ?_
  have h := σUV.coe_rangeProj_add_coe_complProj k (σUV.projSpace k (c.discrepancy σU σV k z))
  rw [SmoothCohomologySplitting.coe_projSpace] at h
  have hL := σUV.overlapProj_overlapLift k (c.rangePart σU σV σUV k z)
  rw [SmoothCohomologySplitting.overlapProj_apply] at hL
  have hmem := sub_mem (σUV.sub_proj_mem_exactForms (c.discrepancy σU σV k z))
    (σUV.sub_proj_mem_exactForms (overlapDiff k (σUV.overlapLift k (c.rangePart σU σV σUV k z))))
  rw [← h, hL] at hmem
  convert hmem using 1
  rw [coe_correctedDiscrepancy]
  simp only [rangePart, complementPart, LinearMap.comp_apply]
  abel

/-- The exact part of a closed form `e` on `U ⊓ V` cut off to `U`: zero in degree zero, and
`d (ρ h e)` in positive degree, for the primitive `h` of the splitting on `U ⊓ V`. -/
def exactCorrectionLeft : (k : ℕ) →
    closedForms I (U ⊓ V : Opens M) k →ₗ[ℝ] SmoothForm I U ℝ k
  | 0 => 0
  | j + 1 => mextDerivₗ I j ∘ₗ c.extendLeft ∘ₗ σUV.primitive j

/-- The exact part of a closed form `e` on `U ⊓ V` cut off to `V`: zero in degree zero, and
`d ((1 - ρ) h e)` in positive degree. -/
def exactCorrectionRight : (k : ℕ) →
    closedForms I (U ⊓ V : Opens M) k →ₗ[ℝ] SmoothForm I V ℝ k
  | 0 => 0
  | j + 1 => mextDerivₗ I j ∘ₗ c.extendRight ∘ₗ σUV.primitive j

/-- On `U ⊓ V`, the two exact parts of `e` add up to `e` minus its projection. -/
theorem mpullback_exactCorrectionLeft_add_mpullback_exactCorrectionRight
    (e : closedForms I (U ⊓ V : Opens M) k) :
    SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _)
        (c.exactCorrectionLeft σUV k e) +
      SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _)
        (c.exactCorrectionRight σUV k e) =
        (e : SmoothForm I (U ⊓ V : Opens M) ℝ k) - σUV.proj k e := by
  cases k with
  | zero => simp [exactCorrectionLeft, exactCorrectionRight]
  | succ j =>
    simp only [exactCorrectionLeft, exactCorrectionRight, LinearMap.comp_apply,
      mpullback_mextDerivₗ_extendLeft_add_mpullback_mextDerivₗ_extendRight,
      SmoothCohomologySplitting.mextDerivₗ_primitive]

/-- The exact part cut off to `U` is closed. -/
@[simp]
theorem mextDerivₗ_exactCorrectionLeft (e : closedForms I (U ⊓ V : Opens M) k) :
    mextDerivₗ I k (c.exactCorrectionLeft σUV k e) = 0 := by
  cases k with
  | zero => simp [exactCorrectionLeft]
  | succ j => exact LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I j) _

/-- The exact part cut off to `V` is closed. -/
@[simp]
theorem mextDerivₗ_exactCorrectionRight (e : closedForms I (U ⊓ V : Opens M) k) :
    mextDerivₗ I k (c.exactCorrectionRight σUV k e) = 0 := by
  cases k with
  | zero => simp [exactCorrectionRight]
  | succ j => exact LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I j) _

/-! ### Step 3: gluing -/

/-- The piece on `U` of the new primitive. -/
def primitivePieceLeft (k : ℕ) :
    closedForms I (U ⊔ V : Opens M) (k + 1) →ₗ[ℝ] SmoothForm I U ℝ k :=
  c.primitiveLeft σU σV k -
    (closedForms I U k).subtype ∘ₗ LinearMap.fst _ _ _ ∘ₗ σUV.overlapLift k ∘ₗ
      c.rangePart σU σV σUV k -
    c.exactCorrectionLeft σUV k ∘ₗ c.correctedDiscrepancy σU σV σUV k -
    c.extendLeft ∘ₗ (σUV.overlapCompl k ⊓ σUV.space k).subtype ∘ₗ c.complementPart σU σV σUV k

/-- The piece on `V` of the new primitive. -/
def primitivePieceRight (k : ℕ) :
    closedForms I (U ⊔ V : Opens M) (k + 1) →ₗ[ℝ] SmoothForm I V ℝ k :=
  c.primitiveRight σU σV k -
    (closedForms I V k).subtype ∘ₗ LinearMap.snd _ _ _ ∘ₗ σUV.overlapLift k ∘ₗ
      c.rangePart σU σV σUV k +
    c.exactCorrectionRight σUV k ∘ₗ c.correctedDiscrepancy σU σV σUV k +
    c.extendRight ∘ₗ (σUV.overlapCompl k ⊓ σUV.space k).subtype ∘ₗ c.complementPart σU σV σUV k

/-- The two pieces of the new primitive agree on `U ⊓ V`. -/
theorem mpullback_primitivePieceLeft_eq_mpullback_primitivePieceRight
    (z : closedForms I (U ⊔ V : Opens M) (k + 1)) :
    SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _)
        (c.primitivePieceLeft σU σV σUV k z) =
      SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _)
        (c.primitivePieceRight σU σV σUV k z) := by
  have h₁ := c.mpullback_exactCorrectionLeft_add_mpullback_exactCorrectionRight σUV
    (c.correctedDiscrepancy σU σV σUV k z)
  have h₂ := c.mpullback_extendLeft_add_mpullback_extendRight
    (c.complementPart σU σV σUV k z : SmoothForm I (U ⊓ V : Opens M) ℝ k)
  have h₃ := c.coe_correctedDiscrepancy σU σV σUV z
  rw [c.proj_correctedDiscrepancy] at h₁
  rw [coe_discrepancy, coe_overlapDiff] at h₃
  rw [← sub_eq_zero]
  simp only [primitivePieceLeft, primitivePieceRight, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply, map_sub, map_add, Submodule.subtype_apply, LinearMap.fst_apply,
    LinearMap.snd_apply]
  rw [eq_sub_of_add_eq h₁, eq_sub_of_add_eq h₂, h₃]
  abel

/-- The new primitive: the form on `U ⊔ V` glued from the two pieces. -/
def supPrimitive (k : ℕ) :
    closedForms I (U ⊔ V : Opens M) (k + 1) →ₗ[ℝ] SmoothForm I (U ⊔ V : Opens M) ℝ k :=
  SmoothForm.glueₗ (c.primitivePieceLeft σU σV σUV k) (c.primitivePieceRight σU σV σUV k)
    (c.mpullback_primitivePieceLeft_eq_mpullback_primitivePieceRight σU σV σUV (k := k))

/-- The new projection in positive degree: the fixed closed form of step 1 plus the connecting
form of the component of step 2 in the fixed complement. -/
def supProj (k : ℕ) :
    closedForms I (U ⊔ V : Opens M) (k + 1) →ₗ[ℝ] SmoothForm I (U ⊔ V : Opens M) ℝ (k + 1) :=
  (closedForms I _ _).subtype ∘ₗ c.liftPair σU σV k ∘ₗ σU.projExactPair σV k +
    c.connecting k ∘ₗ Submodule.inclusion (σUV.overlapCompl_inf_space_le_closedForms k) ∘ₗ
      c.complementPart σU σV σUV k

/-- The new space in positive degree: spanned by the fixed closed forms of step 1 and the
connecting forms of the fixed complement of step 2. -/
def supSpace (k : ℕ) : Submodule ℝ (SmoothForm I (U ⊔ V : Opens M) ℝ (k + 1)) :=
  LinearMap.range ((closedForms I _ _).subtype ∘ₗ c.liftPair σU σV k) ⊔
    LinearMap.range (c.connecting k ∘ₗ
      Submodule.inclusion (σUV.overlapCompl_inf_space_le_closedForms k))

/-- The restriction to `U` of the new primitive is its piece on `U`. -/
@[simp]
theorem mpullback_supPrimitive_left (z : closedForms I (U ⊔ V : Opens M) (k + 1)) :
    SmoothForm.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _)
      (c.supPrimitive σU σV σUV k z) = c.primitivePieceLeft σU σV σUV k z :=
  SmoothForm.mpullback_glueₗ_left _ _ _ z

/-- The restriction to `V` of the new primitive is its piece on `V`. -/
@[simp]
theorem mpullback_supPrimitive_right (z : closedForms I (U ⊔ V : Opens M) (k + 1)) :
    SmoothForm.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _)
      (c.supPrimitive σU σV σUV k z) = c.primitivePieceRight σU σV σUV k z :=
  SmoothForm.mpullback_glueₗ_right _ _ _ z

/-- The definition of the new projection. -/
theorem supProj_def (k : ℕ) :
    c.supProj σU σV σUV k =
      (closedForms I _ _).subtype ∘ₗ c.liftPair σU σV k ∘ₗ σU.projExactPair σV k +
        c.connecting k ∘ₗ Submodule.inclusion (σUV.overlapCompl_inf_space_le_closedForms k) ∘ₗ
          c.complementPart σU σV σUV k :=
  (rfl)

/-- The forms of the new space are the sums of a fixed closed form of step 1 and a connecting
form of the fixed complement of step 2. -/
theorem mem_supSpace_iff {s : SmoothForm I (U ⊔ V : Opens M) ℝ (k + 1)} :
    s ∈ c.supSpace σU σV σUV k ↔ ∃ p e, (c.liftPair σU σV k p : SmoothForm _ _ ℝ (k + 1)) +
      c.connecting k (Submodule.inclusion (σUV.overlapCompl_inf_space_le_closedForms k) e) = s := by
  simp only [supSpace, Submodule.mem_sup, LinearMap.mem_range, LinearMap.comp_apply,
    Submodule.subtype_apply]
  exact ⟨fun ⟨_, ⟨p, hp⟩, _, ⟨e, he⟩, h⟩ ↦ ⟨p, e, hp ▸ he ▸ h⟩,
    fun ⟨p, e, h⟩ ↦ ⟨_, ⟨p, rfl⟩, _, ⟨e, rfl⟩, h⟩⟩

/-- The new projection takes its values in the new space. -/
theorem supProj_mem (z : closedForms I (U ⊔ V : Opens M) (k + 1)) :
    c.supProj σU σV σUV k z ∈ c.supSpace σU σV σUV k :=
  add_mem (Submodule.mem_sup_left (LinearMap.mem_range_self _ _))
    (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))

/-- The new space consists of closed forms. -/
theorem supSpace_le_closedForms (k : ℕ) :
    c.supSpace σU σV σUV k ≤ closedForms I (U ⊔ V : Opens M) (k + 1) := by
  refine sup_le ?_ ?_ <;> rintro _ ⟨x, rfl⟩
  · exact Submodule.coe_mem _
  · exact c.connecting_mem_closedForms _

instance finiteDimensional_supSpace (k : ℕ) : FiniteDimensional ℝ (c.supSpace σU σV σUV k) :=
  have : FiniteDimensional ℝ (σUV.overlapCompl k ⊓ σUV.space k : Submodule ℝ _) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have := Module.Finite.range ((closedForms I _ _).subtype ∘ₗ c.liftPair σU σV k)
  have := Module.Finite.range (c.connecting k ∘ₗ
      Submodule.inclusion (σUV.overlapCompl_inf_space_le_closedForms k))
  Submodule.finiteDimensional_sup _ _

/-- The new primitive is a primitive of the difference between a closed form and its new
projection. -/
theorem mextDerivₗ_supPrimitive (z : closedForms I (U ⊔ V : Opens M) (k + 1)) :
    mextDerivₗ I k (c.supPrimitive σU σV σUV k z) =
      (z : SmoothForm I (U ⊔ V : Opens M) ℝ (k + 1)) - c.supProj σU σV σUV k z := by
  apply SmoothForm.injective_mayerVietoris U V
  rw [LinearMap.prod_apply, LinearMap.prod_apply, Function.prod_apply, Function.prod_apply,
    Prod.mk.injEq]
  simp only [← SmoothForm.mextDerivₗ_mpullback, mpullback_supPrimitive_left,
    mpullback_supPrimitive_right, supProj_def, LinearMap.add_apply, LinearMap.comp_apply,
    map_sub, map_add, mpullback_connecting_left, mpullback_connecting_right,
    Submodule.coe_inclusion, Submodule.subtype_apply, primitivePieceLeft, primitivePieceRight,
    LinearMap.sub_apply, LinearMap.fst_apply, LinearMap.snd_apply, mextDerivₗ_primitiveLeft,
    mextDerivₗ_primitiveRight, mextDerivₗ_exactCorrectionLeft, mextDerivₗ_exactCorrectionRight,
    coe_exactOnPieces,
    (mem_closedForms_iff_mextDerivₗ_eq_zero I _).mp (σUV.overlapLift k _).1.property,
    (mem_closedForms_iff_mextDerivₗ_eq_zero I _).mp (σUV.overlapLift k _).2.property]
  constructor <;> abel

/-! ### Step 4: the new space maps isomorphically onto cohomology -/

/-- A form of the new space that is exact vanishes. -/
theorem eq_zero_of_mem_supSpace {s : SmoothForm I (U ⊔ V : Opens M) ℝ (k + 1)}
    (hs : s ∈ c.supSpace σU σV σUV k) (hex : s ∈ exactForms I (U ⊔ V : Opens M) (k + 1)) :
    s = 0 := by
  obtain ⟨_, ⟨p, rfl⟩, _, ⟨e, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hs
  rw [exactForms_succ] at hex
  obtain ⟨β, hβ⟩ := hex
  have hU := congrArg (SmoothForm.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _))
    hβ
  have hV := congrArg (SmoothForm.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _))
    hβ
  simp only [← SmoothForm.mextDerivₗ_mpullback, map_add, LinearMap.comp_apply,
    Submodule.subtype_apply, mpullback_connecting_left, mpullback_connecting_right,
    Submodule.coe_inclusion] at hU hV
  -- The fixed closed form vanishes, since its restrictions to `U` and `V` are exact.
  have hp := congrArg Subtype.val (c.projExactPair_liftPair σU σV p)
  rw [SmoothCohomologySplitting.coe_projExactPair, SmoothCohomologySplitting.projPair_apply]
    at hp
  have hp₁ : (p : SmoothForm I U ℝ (k + 1) × SmoothForm I V ℝ (k + 1)).1 = 0 := by
    rw [← congrArg Prod.fst hp, σU.proj_eq_zero_iff, closedForms.coe_mpullback, exactForms_succ]
    exact ⟨SmoothForm.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) β -
      c.extendLeft (e : SmoothForm I (U ⊓ V : Opens M) ℝ k),
      by rw [map_sub, hU, add_sub_cancel_right]⟩
  have hp₂ : (p : SmoothForm I U ℝ (k + 1) × SmoothForm I V ℝ (k + 1)).2 = 0 := by
    rw [← congrArg Prod.snd hp, σV.proj_eq_zero_iff, closedForms.coe_mpullback, exactForms_succ]
    exact ⟨SmoothForm.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) β +
      c.extendRight (e : SmoothForm I (U ⊓ V : Opens M) ℝ k),
      by rw [map_add, hV, neg_add_cancel_right]⟩
  have hp0 : p = 0 := Subtype.ext (Prod.ext hp₁ hp₂)
  subst hp0
  simp only [LinearMap.map_zero, Submodule.coe_zero, zero_add] at hU hV ⊢
  -- The component in the fixed complement lies in the range of `overlapProj`, so it vanishes.
  have hxU : mextDerivₗ I k (c.extendLeft (e : SmoothForm I (U ⊓ V : Opens M) ℝ k) -
      SmoothForm.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) β) = 0 := by
    rw [map_sub, hU, sub_self]
  have hxV : mextDerivₗ I k (-c.extendRight (e : SmoothForm I (U ⊓ V : Opens M) ℝ k) -
      SmoothForm.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) β) = 0 := by
    rw [map_sub, map_neg, hV, sub_self]
  let x : closedForms I U k × closedForms I V k :=
    (⟨_, (mem_closedForms_iff_mextDerivₗ_eq_zero I _).mpr hxU⟩,
      ⟨_, (mem_closedForms_iff_mextDerivₗ_eq_zero I _).mpr hxV⟩)
  have hdiff : (overlapDiff k x : SmoothForm I (U ⊓ V : Opens M) ℝ k) = e := by
    rw [coe_overlapDiff]
    dsimp only [x]
    simp only [map_sub, map_neg, SmoothForm.mpullback_inclusion_inf_sup_left_eq_right]
    refine Eq.trans ?_
      (c.mpullback_extendLeft_add_mpullback_extendRight (e : SmoothForm I (U ⊓ V : Opens M) ℝ k))
    abel
  have hrange : (e : SmoothForm I (U ⊓ V : Opens M) ℝ k) ∈
      LinearMap.range (σUV.overlapProj k) := by
    refine ⟨x, ?_⟩
    rw [SmoothCohomologySplitting.overlapProj_apply]
    exact σUV.proj_eq_of_sub_mem_exactForms e.property.2 (by rw [hdiff, sub_self]; exact zero_mem _)
  have he : e = 0 := Subtype.ext <|
    (Submodule.disjoint_def.mp (σUV.isCompl_overlapCompl k).disjoint) _ hrange e.property.1
  simp [he]

/-! ### Smoothness in families

The lemmas of this section hold when the splittings `σU`, `σV`, and for some also `σUV`,
are smooth (`SmoothCohomologySplitting.IsSmooth`); each docstring names the ones it needs. -/

section Smooth

variable {σU σV σUV} (hσU : σU.IsSmooth.{uE, uH, uN}) (hσV : σV.IsSmooth.{uE, uH, uN})
  (hσUV : σUV.IsSmooth.{uE, uH, uN})
include hσU hσV

section Families

variable {EN : Type uE} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type uH}
  [TopologicalSpace HN] {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
  {J : ModelWithCorners ℝ EN HN} [IsManifold J ∞ N]
  {α : N → closedForms I (U ⊔ V : Opens M) (k + 1)}
  (hα : IsSmoothFamily J (fun t ↦ (α t : SmoothForm I (U ⊔ V : Opens M) ℝ (k + 1))))
include hα

omit c in
/-- The linear functionals of `projExactPair` along a smooth family are smooth,
when `σU` and `σV` are smooth. -/
theorem contMDiff_dual_projExactPair (f : Module.Dual ℝ (σU.exactPairs σV (k + 1))) :
    ContMDiff J 𝓘(ℝ) ∞ (fun t ↦ f (σU.projExactPair σV k (α t))) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  have h : ∀ t, f (σU.projExactPair σV k (α t)) =
      (g ∘ₗ LinearMap.inl ℝ _ _ ∘ₗ (σU.space (k + 1)).subtype)
          (σU.projSpace (k + 1) (closedForms.mpullback (Opens.inclusion le_sup_left)
            (contMDiff_inclusion _) (k + 1) (α t))) +
        (g ∘ₗ LinearMap.inr ℝ _ _ ∘ₗ (σV.space (k + 1)).subtype)
          (σV.projSpace (k + 1) (closedForms.mpullback (Opens.inclusion le_sup_right)
            (contMDiff_inclusion _) (k + 1) (α t))) := fun t ↦ by
    rw [← hg, LinearMap.comp_apply, Submodule.subtype_apply,
      SmoothCohomologySplitting.coe_projExactPair, SmoothCohomologySplitting.projPair_apply]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply,
      SmoothCohomologySplitting.coe_projSpace, LinearMap.inl_apply, LinearMap.inr_apply,
      ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  simp only [h]
  exact ((hσU.preservesSmoothFamilies_subtype_comp_projSpace (k + 1)).contMDiff_dual_apply
    (by simpa only [closedForms.coe_mpullback] using
      hα.mpullback _ (contMDiff_inclusion le_sup_left)) _).add
    ((hσV.preservesSmoothFamilies_subtype_comp_projSpace (k + 1)).contMDiff_dual_apply
    (by simpa only [closedForms.coe_mpullback] using
      hα.mpullback _ (contMDiff_inclusion le_sup_right)) _)

/-- The fixed closed forms of step 1 along a smooth family form a smooth family,
when `σU` and `σV` are smooth. -/
theorem isSmoothFamily_liftPair :
    IsSmoothFamily J (fun t ↦ ((c.liftPair σU σV k (σU.projExactPair σV k (α t)) :
      closedForms I (U ⊔ V : Opens M) (k + 1)) : SmoothForm I (U ⊔ V : Opens M) ℝ (k + 1))) := by
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply] using isSmoothFamily_of_contMDiff_dual
    ((closedForms I (U ⊔ V : Opens M) (k + 1)).subtype ∘ₗ c.liftPair σU σV k)
    (x := fun t ↦ σU.projExactPair σV k (α t)) (contMDiff_dual_projExactPair hσU hσV hα)

/-- `exactOnPieces` along a smooth family is a smooth family, when `σU` and `σV` are smooth. -/
theorem isSmoothFamily_exactOnPieces :
    IsSmoothFamily J (fun t ↦ (c.exactOnPieces σU σV k (α t) :
      SmoothForm I (U ⊔ V : Opens M) ℝ (k + 1))) := by
  simpa only [coe_exactOnPieces] using hα.sub (c.isSmoothFamily_liftPair hσU hσV hα)

/-- `primitiveLeft` along a smooth family is a smooth family, when `σU` and `σV` are smooth. -/
theorem isSmoothFamily_primitiveLeft :
    IsSmoothFamily J (fun t ↦ c.primitiveLeft σU σV k (α t)) :=
  preservesSmoothFamilies_def.mp (hσU.preservesSmoothFamilies_primitive k)
    (fun t ↦ closedForms.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) (k + 1)
      (c.exactOnPieces σU σV k (α t))) (by
    simpa only [closedForms.coe_mpullback] using
      (c.isSmoothFamily_exactOnPieces hσU hσV hα).mpullback _ (contMDiff_inclusion le_sup_left))

/-- `primitiveRight` along a smooth family is a smooth family, when `σU` and `σV` are smooth. -/
theorem isSmoothFamily_primitiveRight :
    IsSmoothFamily J (fun t ↦ c.primitiveRight σU σV k (α t)) :=
  preservesSmoothFamilies_def.mp (hσV.preservesSmoothFamilies_primitive k)
    (fun t ↦ closedForms.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) (k + 1)
      (c.exactOnPieces σU σV k (α t))) (by
    simpa only [closedForms.coe_mpullback] using
      (c.isSmoothFamily_exactOnPieces hσU hσV hα).mpullback _ (contMDiff_inclusion le_sup_right))

/-- The discrepancy along a smooth family is a smooth family, when `σU` and `σV` are smooth. -/
theorem isSmoothFamily_discrepancy :
    IsSmoothFamily J (fun t ↦ (c.discrepancy σU σV k (α t) :
      SmoothForm I (U ⊓ V : Opens M) ℝ k)) := by
  simpa only [coe_discrepancy] using
    ((c.isSmoothFamily_primitiveLeft hσU hσV hα).mpullback _ (contMDiff_inclusion _)).sub
      ((c.isSmoothFamily_primitiveRight hσU hσV hα).mpullback _ (contMDiff_inclusion _))

include hσUV in
/-- The fixed closed forms on `U` of step 2 along a smooth family form a smooth family,
when `σU`, `σV` and `σUV` are smooth. -/
theorem isSmoothFamily_overlapLift_fst :
    IsSmoothFamily J (fun t ↦ ((σUV.overlapLift k (c.rangePart σU σV σUV k (α t))).1 :
      SmoothForm I U ℝ k)) :=
  preservesSmoothFamilies_def.mp
    ((hσUV.preservesSmoothFamilies_subtype_comp_projSpace k).comp_of_finiteDimensional
    ((closedForms I U k).subtype ∘ₗ LinearMap.fst ℝ (closedForms I U k) (closedForms I V k) ∘ₗ
      σUV.overlapLift k ∘ₗ σUV.rangeProj k)) _
    (c.isSmoothFamily_discrepancy hσU hσV hα)

include hσUV in
/-- The fixed closed forms on `V` of step 2 along a smooth family form a smooth family,
when `σU`, `σV` and `σUV` are smooth. -/
theorem isSmoothFamily_overlapLift_snd :
    IsSmoothFamily J (fun t ↦ ((σUV.overlapLift k (c.rangePart σU σV σUV k (α t))).2 :
      SmoothForm I V ℝ k)) :=
  preservesSmoothFamilies_def.mp
    ((hσUV.preservesSmoothFamilies_subtype_comp_projSpace k).comp_of_finiteDimensional
    ((closedForms I V k).subtype ∘ₗ LinearMap.snd ℝ (closedForms I U k) (closedForms I V k) ∘ₗ
      σUV.overlapLift k ∘ₗ σUV.rangeProj k)) _
    (c.isSmoothFamily_discrepancy hσU hσV hα)

include hσUV in
/-- The corrected discrepancy along a smooth family is a smooth family,
when `σU`, `σV` and `σUV` are smooth. -/
theorem isSmoothFamily_correctedDiscrepancy :
    IsSmoothFamily J (fun t ↦ (c.correctedDiscrepancy σU σV σUV k (α t) :
      SmoothForm I (U ⊓ V : Opens M) ℝ k)) := by
  simpa only [coe_correctedDiscrepancy, coe_overlapDiff] using
    (c.isSmoothFamily_discrepancy hσU hσV hα).sub
    (((c.isSmoothFamily_overlapLift_fst hσU hσV hσUV hα).mpullback _ (contMDiff_inclusion _)).sub
      ((c.isSmoothFamily_overlapLift_snd hσU hσV hσUV hα).mpullback _ (contMDiff_inclusion _)))

include hσUV in
/-- The exact part cut off to `U` of the corrected discrepancy along a smooth family is a smooth
family, when `σU`, `σV` and `σUV` are smooth. -/
theorem isSmoothFamily_exactCorrectionLeft :
    IsSmoothFamily J (fun t ↦
      c.exactCorrectionLeft σUV k (c.correctedDiscrepancy σU σV σUV k (α t))) := by
  cases k with
  | zero => simpa [exactCorrectionLeft] using isSmoothFamily_const (J := J) 0
  | succ j =>
    exact (c.isSmoothFamily_extendLeft
      (preservesSmoothFamilies_def.mp (hσUV.preservesSmoothFamilies_primitive j) _
      (c.isSmoothFamily_correctedDiscrepancy hσU hσV hσUV hα))).mextDeriv

include hσUV in
/-- The exact part cut off to `V` of the corrected discrepancy along a smooth family is a smooth
family, when `σU`, `σV` and `σUV` are smooth. -/
theorem isSmoothFamily_exactCorrectionRight :
    IsSmoothFamily J (fun t ↦
      c.exactCorrectionRight σUV k (c.correctedDiscrepancy σU σV σUV k (α t))) := by
  cases k with
  | zero => simpa [exactCorrectionRight] using isSmoothFamily_const (J := J) 0
  | succ j =>
    exact (c.isSmoothFamily_extendRight
      (preservesSmoothFamilies_def.mp (hσUV.preservesSmoothFamilies_primitive j) _
      (c.isSmoothFamily_correctedDiscrepancy hσU hσV hσUV hα))).mextDeriv

include hσUV in
/-- Any linear map applied to the component of step 2 in the fixed complement along a smooth
family gives a smooth family, when `σU`, `σV` and `σUV` are smooth. -/
theorem isSmoothFamily_complementPart_comp
    {l : ℕ} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
    (L : (σUV.overlapCompl k ⊓ σUV.space k : Submodule ℝ _) →ₗ[ℝ] SmoothForm I M' ℝ l) :
    IsSmoothFamily J (fun t ↦ L (c.complementPart σU σV σUV k (α t))) :=
  preservesSmoothFamilies_def.mp
    ((hσUV.preservesSmoothFamilies_subtype_comp_projSpace k).comp_of_finiteDimensional
    (L ∘ₗ σUV.complProj k)) _
    (c.isSmoothFamily_discrepancy hσU hσV hα)

end Families

include hσUV in
/-- The new projection takes smooth families to smooth families,
when `σU`, `σV` and `σUV` are smooth. -/
theorem preservesSmoothFamilies_supProj (k : ℕ) :
    PreservesSmoothFamilies.{uE, uH, uN} (c.supProj σU σV σUV k) :=
    preservesSmoothFamilies_def.mpr fun α hα ↦ by
  simpa only [supProj_def, LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply] using
    (c.isSmoothFamily_liftPair hσU hσV hα).add (c.isSmoothFamily_complementPart_comp hσU hσV hσUV hα
      (c.connecting k ∘ₗ Submodule.inclusion (σUV.overlapCompl_inf_space_le_closedForms k)))

include hσUV in
/-- The new primitive takes smooth families to smooth families,
when `σU`, `σV` and `σUV` are smooth. -/
theorem preservesSmoothFamilies_supPrimitive (k : ℕ) :
    PreservesSmoothFamilies.{uE, uH, uN} (c.supPrimitive σU σV σUV k) :=
    preservesSmoothFamilies_def.mpr fun α hα ↦ by
  refine isSmoothFamily_iff_mpullback_inclusion_sup.mpr ⟨?_, ?_⟩
  · simpa only [mpullback_supPrimitive_left, primitivePieceLeft,
      LinearMap.sub_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.fst_apply]
      using (((c.isSmoothFamily_primitiveLeft hσU hσV hα).sub
        (c.isSmoothFamily_overlapLift_fst hσU hσV hσUV hα)).sub
        (c.isSmoothFamily_exactCorrectionLeft hσU hσV hσUV hα)).sub
        (c.isSmoothFamily_complementPart_comp hσU hσV hσUV hα
          (c.extendLeft ∘ₗ (σUV.overlapCompl k ⊓ σUV.space k).subtype))
  · simpa only [mpullback_supPrimitive_right, primitivePieceRight,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.snd_apply]
      using (((c.isSmoothFamily_primitiveRight hσU hσV hα).sub
        (c.isSmoothFamily_overlapLift_snd hσU hσV hσUV hα)).add
        (c.isSmoothFamily_exactCorrectionRight hσU hσV hσUV hα)).add
        (c.isSmoothFamily_complementPart_comp hσU hσV hσUV hα
          (c.extendRight ∘ₗ (σUV.overlapCompl k ⊓ σUV.space k).subtype))

end Smooth

end MayerVietorisCutoff

/-! ### The splitting on `U ⊔ V` -/

namespace SmoothCohomologySplitting

variable [IsManifold I ∞ M]

/-- If `U` and `V` have smooth cohomology splittings, the closed `0`-forms on `U ⊔ V` form a
finite-dimensional space: they embed, by restriction, into the closed `0`-forms on `U` and on `V`,
which lie in the spaces of the splittings. -/
theorem finiteDimensional_closedForms_zero_sup (σU : SmoothCohomologySplitting I U)
    (σV : SmoothCohomologySplitting I V) :
    FiniteDimensional ℝ (closedForms I (U ⊔ V : Opens M) 0) := by
  have hU : closedForms I U 0 ≤ σU.space 0 := fun z hz ↦ by
    simpa using σU.proj_mem 0 ⟨z, hz⟩
  have hV : closedForms I V 0 ≤ σV.space 0 := fun z hz ↦ by
    simpa using σV.proj_mem 0 ⟨z, hz⟩
  have := Submodule.finiteDimensional_of_le hU
  have := Submodule.finiteDimensional_of_le hV
  have := isNoetherian_of_isNoetherianRing_of_finite ℝ (closedForms I U 0)
  have := isNoetherian_of_isNoetherianRing_of_finite ℝ (closedForms I V 0)
  have := isNoetherian_prod (R := ℝ) (M := closedForms I U 0) (N := closedForms I V 0)
  refine Module.Finite.of_injective
    ((closedForms.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) 0).prod
      (closedForms.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) 0))
    fun z w h ↦ Subtype.ext (SmoothForm.injective_mayerVietoris U V ?_)
  have h₁ := congrArg (fun x : closedForms I U 0 × closedForms I V 0 ↦
    (x.1 : SmoothForm I U ℝ 0)) h
  have h₂ := congrArg (fun x : closedForms I U 0 × closedForms I V 0 ↦
    (x.2 : SmoothForm I V ℝ 0)) h
  simp only [LinearMap.prod_apply, Function.prod_apply, closedForms.coe_mpullback] at h₁ h₂
  simp only [LinearMap.prod_apply, Function.prod_apply, h₁, h₂]

/-- **The Mayer–Vietoris step.** The cohomology splitting of `U ⊔ V` built from splittings of
`U`, `V` and `U ⊓ V` and a cut-off function `c`; it is smooth when the three splittings are
(`SmoothCohomologySplitting.IsSmooth.sup`). -/
def sup (c : MayerVietorisCutoff I U V) (σU : SmoothCohomologySplitting I U)
    (σV : SmoothCohomologySplitting I V) (σUV : SmoothCohomologySplitting I (U ⊓ V : Opens M)) :
    SmoothCohomologySplitting I (U ⊔ V : Opens M) where
  space
    | 0 => closedForms I _ 0
    | k + 1 => c.supSpace σU σV σUV k
  space_le_closedForms
    | 0 => le_rfl
    | k + 1 => c.supSpace_le_closedForms σU σV σUV k
  finiteDimensional_space
    | 0 => σU.finiteDimensional_closedForms_zero_sup σV
    | k + 1 => c.finiteDimensional_supSpace σU σV σUV k
  proj
    | 0 => (closedForms I _ 0).subtype
    | k + 1 => c.supProj σU σV σUV k
  proj_mem
    | 0, z => z.property
    | k + 1, z => c.supProj_mem σU σV σUV z
  proj_zero z := Submodule.subtype_apply z
  primitive k := c.supPrimitive σU σV σUV k
  mextDerivₗ_primitive _ z := c.mextDerivₗ_supPrimitive σU σV σUV z
  eq_zero_of_mem_exactForms k := match k with
    | 0 => fun _ h ↦ by simpa using h
    | k + 1 => fun hs h ↦ c.eq_zero_of_mem_supSpace σU σV σUV hs h

section Sup

variable (c : MayerVietorisCutoff I U V) (σU : SmoothCohomologySplitting I U)
  (σV : SmoothCohomologySplitting I V) (σUV : SmoothCohomologySplitting I (U ⊓ V : Opens M))

/-- In degree zero, the space of `sup` is the space of all closed `0`-forms. -/
theorem space_sup_zero : (sup c σU σV σUV).space 0 = closedForms I (U ⊔ V : Opens M) 0 :=
  (rfl)

/-- In positive degree, the space of `sup` is `MayerVietorisCutoff.supSpace`. -/
theorem space_sup_succ (k : ℕ) : (sup c σU σV σUV).space (k + 1) = c.supSpace σU σV σUV k :=
  (rfl)

/-- In degree zero, the projection of `sup` is the inclusion of the closed `0`-forms. -/
theorem proj_sup_zero : (sup c σU σV σUV).proj 0 = (closedForms I (U ⊔ V : Opens M) 0).subtype :=
  (rfl)

/-- In positive degree, the projection of `sup` is `MayerVietorisCutoff.supProj`. -/
theorem proj_sup_succ (k : ℕ) : (sup c σU σV σUV).proj (k + 1) = c.supProj σU σV σUV k :=
  (rfl)

/-- The primitive of `sup` is `MayerVietorisCutoff.supPrimitive`. -/
theorem primitive_sup (k : ℕ) : (sup c σU σV σUV).primitive k = c.supPrimitive σU σV σUV k :=
  (rfl)

variable {σU σV σUV} in
/-- The Mayer–Vietoris step keeps smoothness: if the splittings of `U`, `V` and `U ⊓ V` are
smooth, so is `sup c σU σV σUV`. -/
theorem IsSmooth.sup (hσU : σU.IsSmooth.{uE, uH, uN}) (hσV : σV.IsSmooth.{uE, uH, uN})
    (hσUV : σUV.IsSmooth.{uE, uH, uN}) : (sup c σU σV σUV).IsSmooth.{uE, uH, uN} where
  preservesSmoothFamilies_proj
    | 0 => by
      rw [proj_sup_zero]
      exact preservesSmoothFamilies_subtype
    | k + 1 => by
      rw [proj_sup_succ]
      exact c.preservesSmoothFamilies_supProj hσU hσV hσUV k
  preservesSmoothFamilies_primitive k := by
    rw [primitive_sup]
    exact c.preservesSmoothFamilies_supPrimitive hσU hσV hσUV k

end Sup

end SmoothCohomologySplitting

/-- **The Mayer–Vietoris step for smooth cohomology splittings.** On a Hausdorff σ-compact
manifold modelled on a finite-dimensional space, if two open sets `U` and `V` and their
intersection have smooth cohomology splittings, then so does their union. -/
theorem SmoothCohomologySplitting.exists_isSmooth_sup [FiniteDimensional ℝ E]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] (U V : Opens M)
    (hU : ∃ σ : SmoothCohomologySplitting I U, σ.IsSmooth.{uE, uH, uN})
    (hV : ∃ σ : SmoothCohomologySplitting I V, σ.IsSmooth.{uE, uH, uN})
    (hUV : ∃ σ : SmoothCohomologySplitting I (U ⊓ V : Opens M), σ.IsSmooth.{uE, uH, uN}) :
    ∃ σ : SmoothCohomologySplitting I (U ⊔ V : Opens M), σ.IsSmooth.{uE, uH, uN} :=
  let ⟨_, hσU⟩ := hU
  let ⟨_, hσV⟩ := hV
  let ⟨_, hσUV⟩ := hUV
  ⟨_, hσU.sup (MayerVietorisCutoff.nonempty U V).some hσV hσUV⟩

end SymplecticGeometry
