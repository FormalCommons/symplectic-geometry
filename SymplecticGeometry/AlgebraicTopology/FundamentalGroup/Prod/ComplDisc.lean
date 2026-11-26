/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Connected.LocallyPathConnected
public import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Prod.PuncturedDisc

import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Homeomorph.Lemmas
import SymplecticGeometry.Algebra.Category.Grp.Pushout
import SymplecticGeometry.Topology.Connected.Clopen
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic
import TauCeti.Analysis.Normed.Module.Connected

/-!
# Removing a codimension-two product from a space

Let `f : Q × ball c R → X` be an open embedding, with `Q` path connected and `X` connected and
locally path connected, such that `Z = f '' (Q × {c})` is closed. This file shows that the
inclusion `X \ Z → X` induces a surjection of fundamental groups at `f (q, z)`, `z ≠ c`, whose
kernel is the normal closure of the class of the meridian `t ↦ f (q, c + (z - c) e^{2πit})`. When
the meridian is null-homotopic in `X \ Z`, the inclusion induces an isomorphism.

The proof is van Kampen for the cover of `X` by `X \ Z` and the range of `f`, which meet in the
image of `Q × (ball c R \ {c})`. First, for any cover by open sets `A` and `B` with `A`, `B` and
`A ∩ B` path connected, if `π₁(A ∩ B) → π₁(B)` is onto with kernel the normal closure of `S`, then
`π₁(A) → π₁(X)` is onto with kernel the normal closure of the image of `S`: this is Tau Ceti's
`TauCeti.isPushout_fundamentalGroup` together with
`CategoryTheory.IsPushout.ker_inr_eq_normalClosure`. For the cover above, `f` identifies
`π₁(A ∩ B) → π₁(B)` with the map computed in
`FundamentalGroup.ker_map_prodMap_inclusion_ball_diff_singleton_eq_normalClosure`. The complement
`X \ Z` is path connected by `IsPreconnected.of_isOpen_of_union_eq_univ`, since `X` is connected
and the range of `f` meets it in a path connected set.

## Main results

* `FundamentalGroup.map_subtypeVal_surjective_of_map_inclusion_surjective` and
  `FundamentalGroup.ker_map_subtypeVal_eq_normalClosure_image`: the van Kampen statement above
  for a general cover.
* `Topology.IsOpenEmbedding.restrictPuncturedBall`: `f` on `Q × (ball c R \ {c})`, as a map into
  `X \ Z`; the meridian is the image of the loop `(Path.refl q).prod (c.loopAround z)` under it.
* `FundamentalGroup.map_subtypeVal_compl_image_surjective`: the inclusion `X \ Z → X` is onto on
  fundamental groups.
* `FundamentalGroup.ker_map_subtypeVal_compl_image_eq_normalClosure`: its kernel is the normal
  closure of the meridian.
* `FundamentalGroup.map_subtypeVal_compl_image_bijective` and
  `FundamentalGroup.complImageMulEquiv`: if the meridian is null-homotopic in `X \ Z`, the
  inclusion is an isomorphism on fundamental groups.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Theorem 1.20.
-/

public section

open CategoryTheory Metric Set Topology

namespace FundamentalGroup

section VanKampen

variable {X : Type*} [TopologicalSpace X] {A B : Set X} {x : X}

/-- **Van Kampen with a surjective overlap leg, surjectivity.** Let the interiors of `A` and `B`
cover `X`, with `A`, `B` and `A ∩ B` path connected and `x ∈ A ∩ B`. If the inclusion
`A ∩ B → B` induces a surjection of fundamental groups at `x`, then so does `A → X`. -/
theorem map_subtypeVal_surjective_of_map_inclusion_surjective
    (hCover : interior A ∪ interior B = univ) (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAB : IsPathConnected (A ∩ B)) (hxA : x ∈ A) (hxB : x ∈ B)
    (h : Function.Surjective
      (map (ContinuousMap.inclusion inter_subset_right) (⟨x, hxA, hxB⟩ : ↥(A ∩ B)))) :
    Function.Surjective (map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩) :=
  (TauCeti.isPushout_fundamentalGroup hCover hA hB hAB hxA hxB).flip.surjective_inr_of_surjective h

/-- **Van Kampen with a surjective overlap leg, the kernel.** Let the interiors of `A` and `B`
cover `X`, with `A`, `B` and `A ∩ B` path connected and `x ∈ A ∩ B`. If the inclusion
`A ∩ B → B` induces a surjection of fundamental groups at `x` whose kernel is the normal closure
of `S`, then the kernel of the map induced by `A → X` is the normal closure of the image of `S`
under the map induced by `A ∩ B → A`. -/
theorem ker_map_subtypeVal_eq_normalClosure_image
    (hCover : interior A ∪ interior B = univ) (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAB : IsPathConnected (A ∩ B)) (hxA : x ∈ A) (hxB : x ∈ B)
    (h : Function.Surjective
      (map (ContinuousMap.inclusion inter_subset_right) (⟨x, hxA, hxB⟩ : ↥(A ∩ B))))
    {S : Set (FundamentalGroup ↥(A ∩ B) ⟨x, hxA, hxB⟩)}
    (hS : (map (ContinuousMap.inclusion inter_subset_right) (⟨x, hxA, hxB⟩ : ↥(A ∩ B))).ker =
      Subgroup.normalClosure S) :
    (map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩).ker = Subgroup.normalClosure
      (map (ContinuousMap.inclusion inter_subset_left) (⟨x, hxA, hxB⟩ : ↥(A ∩ B)) '' S) := by
  -- the pushout square is stated in `GrpCat`; `GrpCat.Hom.hom (GrpCat.ofHom φ)` is `φ`
  have hker : (map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩).ker = Subgroup.normalClosure
      (map (ContinuousMap.inclusion inter_subset_left) (⟨x, hxA, hxB⟩ : ↥(A ∩ B)) ''
        (map (ContinuousMap.inclusion inter_subset_right) (⟨x, hxA, hxB⟩ : ↥(A ∩ B))).ker) :=
    (TauCeti.isPushout_fundamentalGroup hCover hA hB hAB hxA hxB).flip.ker_inr_eq_normalClosure h
  rw [hker, hS]
  refine le_antisymm (Subgroup.normalClosure_le_normal ?_)
    (Subgroup.normalClosure_mono (image_mono Subgroup.subset_normalClosure))
  rw [image_subset_iff]
  exact fun y hy ↦ Subgroup.comap_normalClosure_image_ge S _ hy

end VanKampen

end FundamentalGroup

namespace Topology.IsOpenEmbedding

variable {Q X : Type*} [TopologicalSpace Q] [TopologicalSpace X] {c : ℂ} {R : ℝ}
  {f : Q × ↥(ball c R) → X}

/-- An open embedding `f : Q × ball c R → X` sends `Q × (ball c R \ {c})` outside
`f '' (Q × {c})`. -/
theorem apply_notMem_image (hf : IsOpenEmbedding f) (q : Q) (z : ↥(ball c R \ {c})) :
    f (q, ⟨z, mem_of_mem_sdiff z.property⟩) ∉ f '' {p | (p.2 : ℂ) = c} := fun ⟨_, hp, hpz⟩ ↦
  notMem_of_mem_sdiff z.property
    (mem_singleton_iff.2 ((congrArg (fun p ↦ (p.2 : ℂ)) (hf.injective hpz)).symm.trans hp))

/-- An open embedding `f : Q × ball c R → X`, restricted to `Q × (ball c R \ {c})`, as a map into
the complement of `f '' (Q × {c})`. -/
def restrictPuncturedBall (hf : IsOpenEmbedding f) :
    C(Q × ↥(ball c R \ {c}), ↥(f '' {p | (p.2 : ℂ) = c})ᶜ) where
  toFun w := ⟨f (w.1, ⟨w.2, mem_of_mem_sdiff w.2.property⟩), hf.apply_notMem_image w.1 w.2⟩
  continuous_toFun := by fun_prop

@[simp]
theorem coe_restrictPuncturedBall_apply (hf : IsOpenEmbedding f) (w : Q × ↥(ball c R \ {c})) :
    (hf.restrictPuncturedBall w : X) = f (w.1, ⟨w.2, mem_of_mem_sdiff w.2.property⟩) :=
  (rfl)

/-- An open embedding `f : Q × ball c R → X` maps `Q × (ball c R \ {c})` onto the part of its
range outside `f '' (Q × {c})`. -/
theorem range_comp_prodMap_inclusion (hf : IsOpenEmbedding f) :
    range (f ∘ (ContinuousMap.id Q).prodMap
      (ContinuousMap.inclusion (sdiff_subset : ball c R \ {c} ⊆ ball c R))) =
      (f '' {p | (p.2 : ℂ) = c})ᶜ ∩ range f := by
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨w, rfl⟩
    exact ⟨hf.apply_notMem_image w.1 w.2, mem_range_self _⟩
  · rintro ⟨hyZ, p, rfl⟩
    exact ⟨(p.1, ⟨p.2, p.2.property, fun h ↦ hyZ ⟨p, h, rfl⟩⟩), rfl⟩

end Topology.IsOpenEmbedding

namespace FundamentalGroup

variable {Q X : Type*} [TopologicalSpace Q] [TopologicalSpace X] {c : ℂ} {R : ℝ}
  {f : Q × ↥(ball c R) → X}

/-- The overlap leg of the van Kampen square for the cover of `X` by the complement of
`f '' (Q × {c})` and the range of `f`: transported along `f`, it is the map of
`map_prodMap_inclusion_ball_diff_singleton_surjective`. -/
private theorem surjective_and_exists_ker_eq (hf : IsOpenEmbedding f) (q : Q)
    (z : ↥(ball c R \ {c})) (x : ↥((f '' {p | (p.2 : ℂ) = c})ᶜ ∩ range f))
    (hx : (x : X) = f (q, ⟨z, mem_of_mem_sdiff z.property⟩)) :
    Function.Surjective (map (ContinuousMap.inclusion inter_subset_right) x) ∧
    ∃ μ, (map (ContinuousMap.inclusion inter_subset_right) x).ker =
        Subgroup.normalClosure {μ} ∧
      map (ContinuousMap.inclusion inter_subset_left) x μ =
        mapOfEq hf.restrictPuncturedBall
          (Subtype.ext hx.symm :
            hf.restrictPuncturedBall (q, z) = ContinuousMap.inclusion inter_subset_left x)
          (fromPath (Path.Homotopic.Quotient.mk ((Path.refl q).prod (c.loopAround z)))) := by
  set F := (ContinuousMap.id Q).prodMap
    (ContinuousMap.inclusion (sdiff_subset : ball c R \ {c} ⊆ ball c R))
  have hg : IsEmbedding (f ∘ F) := hf.isEmbedding.comp
    (IsEmbedding.id.prodMap (IsEmbedding.inclusion sdiff_subset))
  have hrange := hf.range_comp_prodMap_inclusion
  let e' : Q × ↥(ball c R \ {c}) ≃ₜ ↥((f '' {p | (p.2 : ℂ) = c})ᶜ ∩ range f) :=
    hg.toHomeomorph.trans (Homeomorph.setCongr hrange)
  let e : Q × ↥(ball c R) ≃ₜ ↥(range f) := hf.isEmbedding.toHomeomorph
  -- `e'` and `e` are `f` on points, so their basepoint equations are `hx`
  let φ' := homeomorphMulEquivOfEq e' (Subtype.ext hx.symm : e' (q, z) = x)
  let φ := homeomorphMulEquivOfEq e
    (Subtype.ext hx.symm : e (F (q, z)) = ContinuousMap.inclusion inter_subset_right x)
  have hsq : ∀ γ, map (ContinuousMap.inclusion inter_subset_right) x (φ' γ) =
      φ (map F (q, z) γ) := fun γ ↦ by
    simp only [φ, φ', homeomorphMulEquivOfEq_apply, ← mapOfEq_rfl]
    -- both composites are `f ∘ F` on points
    exact mapOfEq_mapOfEq_eq_mapOfEq_mapOfEq (by ext; rfl) _ _ _ _ γ
  set L := map (ContinuousMap.inclusion inter_subset_right) x
  have hcomp : L.comp (φ' : _ →* _) = φ.toMonoidHom.comp (map F (q, z)) := MonoidHom.ext hsq
  refine ⟨fun y ↦ ?_, φ' (fromPath (Path.Homotopic.Quotient.mk
    ((Path.refl q).prod (c.loopAround z)))), ?_, ?_⟩
  · obtain ⟨γ, hγ⟩ := map_prodMap_inclusion_ball_diff_singleton_surjective q z (φ.symm y)
    exact ⟨φ' γ, (hsq γ).trans ((congrArg φ hγ).trans (φ.apply_symm_apply y))⟩
  · have hL : L = (L.comp (φ' : _ →* _)).comp
        (φ'.symm : _ →* FundamentalGroup (Q × ↥(ball c R \ {c})) (q, z)) := by
      ext γ
      simp
    rw [hL, MonoidHom.ker_comp_mulEquiv, hcomp, MonoidHom.ker_comp_of_injective _ _ φ.injective,
      ker_map_prodMap_inclusion_ball_diff_singleton_eq_normalClosure, MulEquiv.symm_symm,
      Subgroup.map_normalClosure _ _ φ'.surjective, image_singleton]
    simp only [MonoidHom.coe_ofClass]
  · simp only [φ', homeomorphMulEquivOfEq_apply, ← mapOfEq_rfl]
    -- `inclusion ∘ e'` is `restrictPuncturedBall` on points
    exact mapOfEq_mapOfEq_eq_mapOfEq (by ext; rfl) _ _ _ _

/-- The hypotheses of van Kampen for the cover of `X` by the complement of `f '' (Q × {c})` and
the range of `f`. -/
private theorem vanKampen_hypotheses [PathConnectedSpace Q] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hf : IsOpenEmbedding f)
    (hZ : IsClosed (f '' {p | (p.2 : ℂ) = c}))
    (z : ↥(ball c R \ {c})) :
    interior (f '' {p | (p.2 : ℂ) = c})ᶜ ∪ interior (range f) = univ ∧
      IsPathConnected (f '' {p | (p.2 : ℂ) = c})ᶜ ∧ IsPathConnected (range f) ∧
      IsPathConnected ((f '' {p | (p.2 : ℂ) = c})ᶜ ∩ range f) := by
  have hR : 0 < R := pos_of_mem_ball (mem_of_mem_sdiff z.property)
  have : PathConnectedSpace ↥(ball c R) := isPathConnected_iff_pathConnectedSpace.1
    ((convex_ball c R).isPathConnected ⟨c, mem_ball_self hR⟩)
  have : PathConnectedSpace ↥(ball c R \ {c}) := isPathConnected_iff_pathConnectedSpace.1
    (TauCeti.isPathConnected_ball_sdiff_singleton (by simp [Complex.rank_real_complex]) c hR)
  have hunion : (f '' {p | (p.2 : ℂ) = c})ᶜ ∪ range f = univ :=
    eq_univ_of_univ_subset ((compl_union_self _).symm.subset.trans
      (union_subset_union_right _ (image_subset_range _ _)))
  have hAB : IsPathConnected ((f '' {p | (p.2 : ℂ) = c})ᶜ ∩ range f) :=
    hf.range_comp_prodMap_inclusion ▸ isPathConnected_range (hf.continuous.comp (map_continuous _))
  refine ⟨by rw [hZ.isOpen_compl.interior_eq, hf.isOpen_range.interior_eq, hunion],
    (hZ.isOpen_compl.isConnected_iff_isPathConnected).1 ⟨hAB.nonempty.mono inter_subset_left,
      hAB.isConnected.isPreconnected.of_isOpen_of_union_eq_univ hAB.nonempty hZ.isOpen_compl
        hf.isOpen_range hunion⟩, isPathConnected_range hf.continuous, hAB⟩

variable [PathConnectedSpace Q] [ConnectedSpace X] [LocallyPathConnectedSpace X]

/-- **Removing a codimension-two product is surjective on fundamental groups.** Let
`f : Q × ball c R → X` be an open embedding into a connected, locally path connected space, with
`Q` path connected and `Z = f '' (Q × {c})` closed. Then the inclusion `X \ Z → X` induces a
surjection of fundamental groups at `f (q, z)`, for every `z ≠ c` in the disc. -/
theorem map_subtypeVal_compl_image_surjective (hf : IsOpenEmbedding f)
    (hZ : IsClosed (f '' {p | (p.2 : ℂ) = c})) (q : Q) (z : ↥(ball c R \ {c})) :
    Function.Surjective (map (ContinuousMap.subtypeVal (f '' {p | (p.2 : ℂ) = c})ᶜ)
      (hf.restrictPuncturedBall (q, z))) :=
  have h := vanKampen_hypotheses hf hZ z
  map_subtypeVal_surjective_of_map_inclusion_surjective h.1 h.2.1 h.2.2.1 h.2.2.2
    (hf.apply_notMem_image q z) (mem_range_self _)
    (surjective_and_exists_ker_eq hf q z
      ⟨_, mem_inter (hf.apply_notMem_image q z) (mem_range_self _)⟩ rfl).1

/-- **The kernel of removing a codimension-two product is normally generated by a meridian.**
Let `f : Q × ball c R → X` be an open embedding into a connected, locally path connected space,
with `Q` path connected and `Z = f '' (Q × {c})` closed. The kernel of the map of fundamental
groups induced by the inclusion `X \ Z → X` at `f (q, z)`, `z ≠ c`, is the normal closure of the
class of the meridian `t ↦ f (q, c + (z - c) e^{2πit})`. -/
theorem ker_map_subtypeVal_compl_image_eq_normalClosure (hf : IsOpenEmbedding f)
    (hZ : IsClosed (f '' {p | (p.2 : ℂ) = c})) (q : Q) (z : ↥(ball c R \ {c})) :
    (map (ContinuousMap.subtypeVal (f '' {p | (p.2 : ℂ) = c})ᶜ)
      (hf.restrictPuncturedBall (q, z))).ker =
      Subgroup.normalClosure {(map hf.restrictPuncturedBall (q, z)
        (fromPath (Path.Homotopic.Quotient.mk ((Path.refl q).prod (c.loopAround z)))))} := by
  have h := vanKampen_hypotheses hf hZ z
  obtain ⟨hsurj, μ, hμ, hμ'⟩ := surjective_and_exists_ker_eq hf q z
    ⟨_, mem_inter (hf.apply_notMem_image q z) (mem_range_self _)⟩ rfl
  refine (ker_map_subtypeVal_eq_normalClosure_image h.1 h.2.1 h.2.2.1 h.2.2.2
    (hf.apply_notMem_image q z) (mem_range_self _) hsurj hμ).trans ?_
  rw [image_singleton, hμ']
  -- the basepoint equation of `hμ'` holds by `rfl`, so `mapOfEq` is `map` here
  exact congrArg (fun g ↦ Subgroup.normalClosure {g})
    (DFunLike.congr_fun (mapOfEq_rfl hf.restrictPuncturedBall) _)

/-- If the meridian `t ↦ f (q, c + (z - c) e^{2πit})` is null-homotopic in `X \ Z`, where `f`,
`Q`, `X` and `Z = f '' (Q × {c})` are as in `ker_map_subtypeVal_compl_image_eq_normalClosure`,
then the inclusion `X \ Z → X` induces a bijection of fundamental groups at `f (q, z)`. -/
theorem map_subtypeVal_compl_image_bijective (hf : IsOpenEmbedding f)
    (hZ : IsClosed (f '' {p | (p.2 : ℂ) = c})) (q : Q) (z : ↥(ball c R \ {c}))
    (h : map hf.restrictPuncturedBall (q, z)
      (fromPath (Path.Homotopic.Quotient.mk ((Path.refl q).prod (c.loopAround z)))) = 1) :
    Function.Bijective (map (ContinuousMap.subtypeVal (f '' {p | (p.2 : ℂ) = c})ᶜ)
      (hf.restrictPuncturedBall (q, z))) := by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).1 ?_, map_subtypeVal_compl_image_surjective hf hZ q z⟩
  rw [ker_map_subtypeVal_compl_image_eq_normalClosure hf hZ q z, h,
    Subgroup.normalClosure_eq_bot_iff.2 subset_rfl]

/-- If the meridian `t ↦ f (q, c + (z - c) e^{2πit})` is null-homotopic in `X \ Z`, the
isomorphism `π₁(X \ Z, f (q, z)) ≃* π₁(X, f (q, z))` induced by the inclusion, with `f`, `Q`, `X`
and `Z = f '' (Q × {c})` as in `ker_map_subtypeVal_compl_image_eq_normalClosure`. -/
noncomputable def complImageMulEquiv (hf : IsOpenEmbedding f)
    (hZ : IsClosed (f '' {p | (p.2 : ℂ) = c})) (q : Q) (z : ↥(ball c R \ {c}))
    (h : map hf.restrictPuncturedBall (q, z)
      (fromPath (Path.Homotopic.Quotient.mk ((Path.refl q).prod (c.loopAround z)))) = 1) :
    FundamentalGroup (↥(f '' {p | (p.2 : ℂ) = c})ᶜ) (hf.restrictPuncturedBall (q, z)) ≃*
      FundamentalGroup X (hf.restrictPuncturedBall (q, z) : X) :=
  MulEquiv.ofBijective _ (map_subtypeVal_compl_image_bijective hf hZ q z h)

@[simp]
theorem complImageMulEquiv_apply (hf : IsOpenEmbedding f)
    (hZ : IsClosed (f '' {p | (p.2 : ℂ) = c})) (q : Q) (z : ↥(ball c R \ {c}))
    (h : map hf.restrictPuncturedBall (q, z)
      (fromPath (Path.Homotopic.Quotient.mk ((Path.refl q).prod (c.loopAround z)))) = 1)
    (γ : FundamentalGroup (↥(f '' {p | (p.2 : ℂ) = c})ᶜ) (hf.restrictPuncturedBall (q, z))) :
    complImageMulEquiv hf hZ q z h γ =
      map (ContinuousMap.subtypeVal (f '' {p | (p.2 : ℂ) = c})ᶜ)
        (hf.restrictPuncturedBall (q, z)) γ :=
  (rfl)

end FundamentalGroup

end
