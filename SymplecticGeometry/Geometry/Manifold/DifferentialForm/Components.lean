/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import Mathlib.Topology.Sets.OpenCover
public import TauCeti.Topology.ConnectedComponents
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens

/-!
# Smooth forms on the members of a disjoint open cover

Let `U : ι → Opens M` be a family of pairwise disjoint open subsets covering a manifold `M`, such
as the connected components of a locally connected space (Tau Ceti's
`ConnectedComponents.opens`, with `ConnectedComponents.pairwise_disjoint_opens` and
`ConnectedComponents.iSup_opens`). A smooth form on `M` is then the same as a family of smooth
forms, one on each `U i`, and closedness and exactness can be tested on the members of the cover.

## Main declarations

* `ConnectedComponents.isConnected_opens`: in a locally connected space, each connected
  component, as an open set, is connected; `ConnectedComponents.connectedSpace_opens` is the
  corresponding instance on the open submanifold.
* `TauCeti.SmoothForm.ofDisjointCover`: the smooth form on `M` glued from a family of smooth
  forms on the `U i`. Its restriction to `U i` is the `i`-th form
  (`TauCeti.SmoothForm.mpullback_subtype_val_ofDisjointCover`).
* `TauCeti.SmoothForm.ext_of_mpullback_subtype_val`: two forms whose restrictions to the members
  of an open cover agree are equal.
* `TauCeti.SmoothForm.disjointCoverEquiv`: restriction to the members of the cover, as a linear
  equivalence from the smooth forms on `M` onto the product of the smooth forms on the `U i`.
* `TauCeti.SmoothForm.mem_closedForms_iff_forall_mpullback_subtype_val` and
  `TauCeti.SmoothForm.mem_exactForms_iff_forall_mpullback_subtype_val`: a real form is closed, or
  exact, exactly when each of its restrictions is. A primitive on `M` is glued from primitives on
  the `U i` by `TauCeti.SmoothForm.ofDisjointCover`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapters 14 and 17.
-/

public section

open Function Set TopologicalSpace
open scoped Manifold ContDiff

namespace ConnectedComponents

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]

/-- In a locally connected space, each connected component, as an open set, is connected. -/
theorem isConnected_opens (C : ConnectedComponents X) : IsConnected (C.opens : Set X) := by
  obtain ⟨x, rfl⟩ := surjective_coe C
  rw [coe_opens_mk]
  exact isConnected_connectedComponent

/-- In a locally connected space, each connected component, as an open subspace, is a connected
space. -/
instance connectedSpace_opens (C : ConnectedComponents X) : ConnectedSpace C.opens :=
  isConnected_iff_connectedSpace.mp C.isConnected_opens

end ConnectedComponents

namespace TauCeti

namespace SmoothForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {ι : Type*} {U : ι → Opens M}

variable [IsManifold I 1 M]

/-- Forms on `M` whose restrictions to the members of an open cover agree are equal. -/
theorem ext_of_mpullback_subtype_val (hcover : IsOpenCover U) {φ ψ : SmoothForm I M F k}
    (h : ∀ i, mpullback (Subtype.val : U i → M) contMDiff_subtypeVal φ =
      mpullback (Subtype.val : U i → M) contMDiff_subtypeVal ψ) :
    φ = ψ := by
  refine Subtype.ext (funext fun x ↦ ?_)
  obtain ⟨i, hx⟩ := hcover.exists_mem x
  have := congrArg (fun σ : SmoothForm I (U i) F k ↦ σ.val ⟨x, hx⟩) (h i)
  exact (coe_mpullback_subtype_val_apply φ ⟨x, hx⟩).symm.trans
    (this.trans (coe_mpullback_subtype_val_apply ψ ⟨x, hx⟩))

/-- The form glued from a family of smooth forms on the members of a disjoint open cover, as a
rough form. At each point it is the value of the form on the member that contains it. -/
private noncomputable def ofDisjointCoverAux (hcover : IsOpenCover U)
    (σ : ∀ i, SmoothForm I (U i) F k) :
    RoughForm I M F k := fun x ↦
  (σ (hcover.exists_mem x).choose).val ⟨x, (hcover.exists_mem x).choose_spec⟩

private theorem ofDisjointCoverAux_apply (hU : Pairwise (Disjoint on U))
    (hcover : IsOpenCover U)
    (σ : ∀ i, SmoothForm I (U i) F k) {i : ι} (x : U i) :
    ofDisjointCoverAux hcover σ x = (σ i).val x := by
  have key : ∀ j (hj : (x : M) ∈ U j), j = i → (σ j).val ⟨x, hj⟩ = (σ i).val x := by
    rintro j hj rfl
    rfl
  refine key _ _ (hU.eq ?_)
  exact fun hd ↦ disjoint_left.mp (Opens.coe_disjoint.mpr hd)
    (hcover.exists_mem x).choose_spec x.property

/-- **Gluing smooth forms over a disjoint open cover.** For pairwise disjoint open subsets `U i`
covering `M`, the smooth form on `M` whose restriction to each `U i` is the `i`-th form of a
family `σ` (`mpullback_subtype_val_ofDisjointCover`). -/
noncomputable def ofDisjointCover (hU : Pairwise (Disjoint on U)) (hcover : IsOpenCover U)
    (σ : ∀ i, SmoothForm I (U i) F k) : SmoothForm I M F k :=
  ⟨ofDisjointCoverAux hcover σ, IsSmoothForm.mem_smoothBundleForms <|
    (isSmoothForm_def ∞ _).mpr fun x ↦ by
      obtain ⟨i, hx⟩ := hcover.exists_mem x
      refine (contMDiffAt_mpullback_subtype_val_iff (U := U i) _ ⟨x, hx⟩).mp ?_
      have : TauCeti.mpullback I I (Subtype.val : U i → M) (ofDisjointCoverAux hcover σ) =
          (σ i).val :=
        funext fun y ↦ by rw [mpullback_subtype_val_apply, ofDisjointCoverAux_apply hU]
      rw [this]
      exact (σ i).contMDiff _⟩

/-- At a point of `U i`, the glued form is the `i`-th form of the family. -/
theorem ofDisjointCover_apply (hU : Pairwise (Disjoint on U)) (hcover : IsOpenCover U)
    (σ : ∀ i, SmoothForm I (U i) F k) {i : ι} (x : U i) :
    (ofDisjointCover hU hcover σ).val x = (σ i).val x :=
  ofDisjointCoverAux_apply hU hcover σ x

/-- The restriction of the glued form to `U i` is the `i`-th form of the family. -/
@[simp]
theorem mpullback_subtype_val_ofDisjointCover (hU : Pairwise (Disjoint on U))
    (hcover : IsOpenCover U) (σ : ∀ i, SmoothForm I (U i) F k) (i : ι) :
    mpullback (Subtype.val : U i → M) contMDiff_subtypeVal (ofDisjointCover hU hcover σ) = σ i :=
  Subtype.ext <| funext fun x ↦ by
    rw [coe_mpullback_subtype_val_apply, ofDisjointCover_apply hU hcover σ x]

/-- Gluing the restrictions of a form to the members of a disjoint open cover gives the form
back. -/
@[simp]
theorem ofDisjointCover_mpullback_subtype_val (hU : Pairwise (Disjoint on U))
    (hcover : IsOpenCover U) (φ : SmoothForm I M F k) :
    ofDisjointCover hU hcover
        (fun i ↦ mpullback (Subtype.val : U i → M) contMDiff_subtypeVal φ) = φ :=
  ext_of_mpullback_subtype_val hcover fun i ↦ mpullback_subtype_val_ofDisjointCover hU hcover _ i

variable (F k) in
/-- For pairwise disjoint open subsets `U i` covering `M`, restriction to the `U i` is a linear
equivalence from the smooth `k`-forms on `M` onto the product of the smooth `k`-forms on the
`U i`. Its inverse glues a family of forms by `ofDisjointCover`. -/
noncomputable def disjointCoverEquiv (hU : Pairwise (Disjoint on U)) (hcover : IsOpenCover U) :
    SmoothForm I M F k ≃ₗ[ℝ] ∀ i, SmoothForm I (U i) F k where
  toFun φ i := mpullback (Subtype.val : U i → M) contMDiff_subtypeVal φ
  map_add' φ ψ := funext fun _ ↦ map_add _ φ ψ
  map_smul' c φ := funext fun _ ↦ map_smul _ c φ
  invFun := ofDisjointCover hU hcover
  left_inv φ := ofDisjointCover_mpullback_subtype_val hU hcover φ
  right_inv σ := funext fun i ↦ mpullback_subtype_val_ofDisjointCover hU hcover σ i

@[simp]
theorem disjointCoverEquiv_apply (hU : Pairwise (Disjoint on U)) (hcover : IsOpenCover U)
    (φ : SmoothForm I M F k) (i : ι) :
    disjointCoverEquiv F k hU hcover φ i =
      mpullback (Subtype.val : U i → M) contMDiff_subtypeVal φ :=
  (rfl)

@[simp]
theorem disjointCoverEquiv_symm_apply (hU : Pairwise (Disjoint on U)) (hcover : IsOpenCover U)
    (σ : ∀ i, SmoothForm I (U i) F k) :
    (disjointCoverEquiv F k hU hcover).symm σ = ofDisjointCover hU hcover σ :=
  (LinearEquiv.symm_apply_eq _).mpr
    (funext fun i ↦ (mpullback_subtype_val_ofDisjointCover hU hcover σ i).symm)

section DeRham

variable [IsManifold I 2 M]

/-- A real form is closed exactly when its restriction to each member of an open cover is
closed. -/
theorem mem_closedForms_iff_forall_mpullback_subtype_val (hcover : IsOpenCover U)
    (φ : SmoothForm I M ℝ k) :
    φ ∈ closedForms I M k ↔
      ∀ i, mpullback (Subtype.val : U i → M) contMDiff_subtypeVal φ ∈ closedForms I (U i) k := by
  simp only [mem_closedForms_iff_mextDerivₗ_eq_zero, mextDerivₗ_mpullback]
  refine ⟨fun h i ↦ by rw [h, map_zero], fun h ↦ ext_of_mpullback_subtype_val hcover fun i ↦ ?_⟩
  rw [h i, map_zero]

/-- A real form is exact exactly when its restriction to each member of a disjoint open cover is
exact. Primitives on the members glue to a primitive on `M`. -/
theorem mem_exactForms_iff_forall_mpullback_subtype_val (hU : Pairwise (Disjoint on U))
    (hcover : IsOpenCover U) (φ : SmoothForm I M ℝ k) :
    φ ∈ exactForms I M k ↔
      ∀ i, mpullback (Subtype.val : U i → M) contMDiff_subtypeVal φ ∈ exactForms I (U i) k := by
  cases k with
  | zero =>
    simp only [exactForms_zero, Submodule.mem_bot]
    refine ⟨fun h i ↦ by rw [h, map_zero], fun h ↦ ext_of_mpullback_subtype_val hcover fun i ↦ ?_⟩
    rw [h i, map_zero]
  | succ k =>
    simp only [exactForms_succ, LinearMap.mem_range]
    refine ⟨fun ⟨ψ, hψ⟩ i ↦ ⟨mpullback Subtype.val contMDiff_subtypeVal ψ, ?_⟩, fun h ↦ ?_⟩
    · rw [mextDerivₗ_mpullback, hψ]
    · choose ψ hψ using h
      refine ⟨ofDisjointCover hU hcover ψ, ext_of_mpullback_subtype_val hcover fun i ↦ ?_⟩
      rw [← mextDerivₗ_mpullback, mpullback_subtype_val_ofDisjointCover, hψ]

end DeRham

end SmoothForm

end TauCeti

end
