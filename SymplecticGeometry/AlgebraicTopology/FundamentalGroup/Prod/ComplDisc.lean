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
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.VanKampen
import SymplecticGeometry.Topology.Connected.Clopen
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.Analysis.Normed.Module.Connected

/-!
# Removing a codimension-two product from a space

Let `f : Q × ball c R → X` be an open embedding, with `Q` path connected and `X` connected and
locally path connected, such that `Z = f '' (Q × {c})` is closed. This file shows that the
inclusion `X \ Z → X` induces a surjection of fundamental groups at `f (q, z)`, `z ≠ c`, whose
kernel is the normal closure of the class of the meridian `t ↦ f (q, c + (z - c) e^{2πit})`. When
the meridian is null-homotopic in `X \ Z`, the inclusion induces an isomorphism.

The proof is van Kampen for the cover of `X` by `X \ Z` and the range of `f`, which meet in the
image of `Q × (ball c R \ {c})`, in the form of
`FundamentalGroup.ker_map_subtypeVal_eq_normalClosure_image`. The map `f` identifies the leg
`π₁((X \ Z) ∩ range f) → π₁(range f)` with the map computed in
`FundamentalGroup.ker_map_prodMap_inclusion_ball_diff_singleton_eq_normalClosure`. The complement
`X \ Z` is path connected by `IsPreconnected.of_isOpen_of_union_eq_univ`, since `X` is connected
and the range of `f` meets it in a path connected set.

Compare Tau Ceti's `TauCeti.fundamentalGroup_map_subtypeVal_compl_singleton_bijective_of_mem_nhds`,
the case of a point removed from a space.

## Main results

* `Topology.IsOpenEmbedding.restrictPuncturedBall`: `f` on `Q × (ball c R \ {c})`, as a map into
  `X \ Z`.
* `Topology.IsOpenEmbedding.meridianLoop` and `Topology.IsOpenEmbedding.meridian`: the meridian
  `t ↦ f (q, c + (z - c) e^{2πit})`, as a loop in `X \ Z`, and its class.
* `Topology.IsOpenEmbedding.isPathConnected_compl_image`: `X \ Z` is path connected.
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

open Metric Set Topology

namespace Function.Injective

variable {Q X : Type*} {c : ℂ} {R : ℝ} {f : Q × ↥(ball c R) → X}

/-- An injective `f : Q × ball c R → X` sends `Q × (ball c R \ {c})` outside `f '' (Q × {c})`. -/
theorem apply_notMem_image_setOfPred_snd_eq (hf : Injective f) (q : Q) (z : ↥(ball c R \ {c})) :
    f (q, ⟨z, mem_of_mem_sdiff z.property⟩) ∉ f '' {p | (p.2 : ℂ) = c} := fun ⟨_, hp, hpz⟩ ↦
  notMem_of_mem_sdiff z.property
    (mem_singleton_iff.2 ((congrArg (fun p ↦ (p.2 : ℂ)) (hf hpz)).symm.trans hp))

variable [TopologicalSpace Q]

/-- An injective `f : Q × ball c R → X` maps `Q × (ball c R \ {c})` onto the part of its range
outside `f '' (Q × {c})`. -/
theorem range_comp_prodMap_inclusion_ball_diff_singleton (hf : Injective f) :
    range (f ∘ (ContinuousMap.id Q).prodMap
      (ContinuousMap.inclusion (sdiff_subset : ball c R \ {c} ⊆ ball c R))) =
      (f '' {p | (p.2 : ℂ) = c})ᶜ ∩ range f := by
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨w, rfl⟩
    exact ⟨hf.apply_notMem_image_setOfPred_snd_eq w.1 w.2, mem_range_self _⟩
  · rintro ⟨hyZ, p, rfl⟩
    exact ⟨(p.1, ⟨p.2, p.2.property, fun h ↦ hyZ ⟨p, h, rfl⟩⟩), rfl⟩

/-- The part of the range of a continuous injective `f : Q × ball c R → X` outside
`f '' (Q × {c})` is path connected, if `Q` is path connected and `R > 0`. -/
theorem isPathConnected_compl_image_inter_range [TopologicalSpace X] [PathConnectedSpace Q]
    (hf : Injective f) (hc : Continuous f) (hR : 0 < R) :
    IsPathConnected ((f '' {p | (p.2 : ℂ) = c})ᶜ ∩ range f) := by
  have : PathConnectedSpace ↥(ball c R \ {c}) := isPathConnected_iff_pathConnectedSpace.1
    (TauCeti.isPathConnected_ball_sdiff_singleton (by simp [Complex.rank_real_complex]) c hR)
  exact hf.range_comp_prodMap_inclusion_ball_diff_singleton ▸
    isPathConnected_range (hc.comp (map_continuous _))

end Function.Injective

namespace Topology.IsOpenEmbedding

variable {Q X : Type*} [TopologicalSpace Q] [TopologicalSpace X] {c : ℂ} {R : ℝ}
  {f : Q × ↥(ball c R) → X}

/-- An open embedding `f : Q × ball c R → X`, restricted to `Q × (ball c R \ {c})`, as a map into
the complement of `f '' (Q × {c})`. -/
def restrictPuncturedBall (hf : IsOpenEmbedding f) :
    C(Q × ↥(ball c R \ {c}), ↥(f '' {p | (p.2 : ℂ) = c})ᶜ) where
  toFun w := ⟨f (w.1, ⟨w.2, mem_of_mem_sdiff w.2.property⟩),
    hf.injective.apply_notMem_image_setOfPred_snd_eq w.1 w.2⟩
  continuous_toFun := by fun_prop

@[simp]
theorem coe_restrictPuncturedBall_apply (hf : IsOpenEmbedding f) (w : Q × ↥(ball c R \ {c})) :
    (hf.restrictPuncturedBall w : X) = f (w.1, ⟨w.2, mem_of_mem_sdiff w.2.property⟩) :=
  (rfl)

/-- The meridian of `f '' (Q × {c})` at `f (q, z)`: the loop `t ↦ f (q, c + (z - c) e^{2πit})` in
the complement of `f '' (Q × {c})`, the image under `restrictPuncturedBall` of the constant loop
at `q` times the loop `Complex.loopAround c z`. -/
noncomputable def meridianLoop (hf : IsOpenEmbedding f) (q : Q) (z : ↥(ball c R \ {c})) :
    Path (hf.restrictPuncturedBall (q, z)) (hf.restrictPuncturedBall (q, z)) :=
  ((Path.refl q).prod (c.loopAround z)).map hf.restrictPuncturedBall.continuous

theorem meridianLoop_def (hf : IsOpenEmbedding f) (q : Q) (z : ↥(ball c R \ {c})) :
    hf.meridianLoop q z =
      ((Path.refl q).prod (c.loopAround z)).map hf.restrictPuncturedBall.continuous :=
  (rfl)

/-- The meridian loop at time `t` is `f (q, w)`, where `w = c + (z - c) e^{2πit}`. -/
theorem coe_meridianLoop_apply (hf : IsOpenEmbedding f) (q : Q) (z : ↥(ball c R \ {c}))
    (t : unitInterval) (w : ↥(ball c R))
    (hw : (w : ℂ) = c + (z - c) * Complex.exp (↑(2 * Real.pi * t) * Complex.I)) :
    (hf.meridianLoop q z t : X) = f (q, w) := by
  rw [meridianLoop_def, Path.map_coe, Function.comp_apply, Path.prod_coe,
    coe_restrictPuncturedBall_apply]
  exact congrArg (fun w ↦ f (q, w)) (Subtype.ext (by simp [hw]))

/-- The meridian class of `f '' (Q × {c})` at `f (q, z)`: the class of `meridianLoop` in the
fundamental group of the complement of `f '' (Q × {c})`. -/
noncomputable def meridian (hf : IsOpenEmbedding f) (q : Q) (z : ↥(ball c R \ {c})) :
    FundamentalGroup ↥(f '' {p | (p.2 : ℂ) = c})ᶜ (hf.restrictPuncturedBall (q, z)) :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (hf.meridianLoop q z))

theorem meridian_def (hf : IsOpenEmbedding f) (q : Q) (z : ↥(ball c R \ {c})) :
    hf.meridian q z =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (hf.meridianLoop q z)) :=
  (rfl)

/-- The meridian class is the image under `restrictPuncturedBall` of the class of the constant
loop at `q` times `Complex.loopAround c z`. -/
theorem map_restrictPuncturedBall_eq_meridian (hf : IsOpenEmbedding f) (q : Q)
    (z : ↥(ball c R \ {c})) :
    FundamentalGroup.map hf.restrictPuncturedBall (q, z)
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((Path.refl q).prod (c.loopAround z)))) =
      hf.meridian q z :=
  TauCeti.FundamentalGroup.map_fromPath hf.restrictPuncturedBall (q, z) _

/-- Let `f : Q × ball c R → X` be an open embedding into a connected, locally path connected space,
with `Q` path connected, `R > 0` and `f '' (Q × {c})` closed. Then the complement of
`f '' (Q × {c})` is path connected. -/
theorem isPathConnected_compl_image [PathConnectedSpace Q] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hf : IsOpenEmbedding f)
    (hZ : IsClosed (f '' {p | (p.2 : ℂ) = c})) (hR : 0 < R) :
    IsPathConnected (f '' {p | (p.2 : ℂ) = c})ᶜ := by
  have hAB := hf.injective.isPathConnected_compl_image_inter_range hf.continuous hR
  exact (hZ.isOpen_compl.isConnected_iff_isPathConnected).1 ⟨hAB.nonempty.mono inter_subset_left,
    hAB.isConnected.isPreconnected.of_isOpen_of_union_eq_univ hAB.nonempty hZ.isOpen_compl
      hf.isOpen_range
      (by rw [← compl_subset_iff_union, compl_compl]; exact image_subset_range _ _)⟩

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
  have hrange := hf.injective.range_comp_prodMap_inclusion_ball_diff_singleton
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

/-- The range of a continuous `f : Q × ball c R → X` is path connected if `Q` is and `R > 0`. -/
private theorem isPathConnected_range_of_pos [PathConnectedSpace Q] (hf : Continuous f)
    (hR : 0 < R) : IsPathConnected (range f) :=
  have : PathConnectedSpace ↥(ball c R) := isPathConnected_iff_pathConnectedSpace.1
    ((convex_ball c R).isPathConnected ⟨c, mem_ball_self hR⟩)
  isPathConnected_range hf

/-- The interiors of the complement of `f '' (Q × {c})` and of the range of `f` cover `X`. -/
private theorem interior_compl_image_union_interior_range (hf : IsOpenEmbedding f)
    (hZ : IsClosed (f '' {p | (p.2 : ℂ) = c})) :
    interior (f '' {p | (p.2 : ℂ) = c})ᶜ ∪ interior (range f) = univ := by
  rw [hZ.isOpen_compl.interior_eq, hf.isOpen_range.interior_eq, ← compl_subset_iff_union,
    compl_compl]
  exact image_subset_range _ _

variable [PathConnectedSpace Q] [ConnectedSpace X] [LocallyPathConnectedSpace X]

/-- **Removing a codimension-two product is surjective on fundamental groups.** Let
`f : Q × ball c R → X` be an open embedding into a connected, locally path connected space, with
`Q` path connected and `Z = f '' (Q × {c})` closed. Then the inclusion `X \ Z → X` induces a
surjection of fundamental groups at `f (q, z)`, for every `z ≠ c` in the disc. -/
theorem map_subtypeVal_compl_image_surjective (hf : IsOpenEmbedding f)
    (hZ : IsClosed (f '' {p | (p.2 : ℂ) = c})) (q : Q) (z : ↥(ball c R \ {c})) :
    Function.Surjective (map (ContinuousMap.subtypeVal (f '' {p | (p.2 : ℂ) = c})ᶜ)
      (hf.restrictPuncturedBall (q, z))) :=
  have hR : 0 < R := pos_of_mem_ball (mem_of_mem_sdiff z.property)
  have hz := hf.injective.apply_notMem_image_setOfPred_snd_eq q z
  map_subtypeVal_surjective_of_map_inclusion_surjective
    (interior_compl_image_union_interior_range hf hZ) (hf.isPathConnected_compl_image hZ hR)
    (isPathConnected_range_of_pos hf.continuous hR)
    (hf.injective.isPathConnected_compl_image_inter_range hf.continuous hR)
    hz (mem_range_self _)
    (surjective_and_exists_ker_eq hf q z ⟨_, mem_inter hz (mem_range_self _)⟩ rfl).1

/-- **The kernel of removing a codimension-two product is normally generated by a meridian.**
Let `f : Q × ball c R → X` be an open embedding into a connected, locally path connected space,
with `Q` path connected and `Z = f '' (Q × {c})` closed. The kernel of the map of fundamental
groups induced by the inclusion `X \ Z → X` at `f (q, z)`, `z ≠ c`, is the normal closure of the
class `hf.meridian q z` of the meridian `t ↦ f (q, c + (z - c) e^{2πit})`. -/
theorem ker_map_subtypeVal_compl_image_eq_normalClosure (hf : IsOpenEmbedding f)
    (hZ : IsClosed (f '' {p | (p.2 : ℂ) = c})) (q : Q) (z : ↥(ball c R \ {c})) :
    (map (ContinuousMap.subtypeVal (f '' {p | (p.2 : ℂ) = c})ᶜ)
      (hf.restrictPuncturedBall (q, z))).ker = Subgroup.normalClosure {hf.meridian q z} := by
  have hR : 0 < R := pos_of_mem_ball (mem_of_mem_sdiff z.property)
  have hz := hf.injective.apply_notMem_image_setOfPred_snd_eq q z
  obtain ⟨hsurj, μ, hμ, hμ'⟩ := surjective_and_exists_ker_eq hf q z
    ⟨_, mem_inter hz (mem_range_self _)⟩ rfl
  refine (ker_map_subtypeVal_eq_normalClosure_image
    (interior_compl_image_union_interior_range hf hZ) (hf.isPathConnected_compl_image hZ hR)
    (isPathConnected_range_of_pos hf.continuous hR)
    (hf.injective.isPathConnected_compl_image_inter_range hf.continuous hR)
    hz (mem_range_self _) hsurj hμ).trans ?_
  rw [image_singleton, hμ', ← hf.map_restrictPuncturedBall_eq_meridian]
  -- the basepoint equation of `hμ'` holds by `rfl`, so `mapOfEq` is `map` here
  exact congrArg (fun g ↦ Subgroup.normalClosure {g})
    (DFunLike.congr_fun (mapOfEq_rfl hf.restrictPuncturedBall) _)

/-- If the meridian class `hf.meridian q z` is trivial, where `f`, `Q`, `X` and
`Z = f '' (Q × {c})` are as in `ker_map_subtypeVal_compl_image_eq_normalClosure`, then the
inclusion `X \ Z → X` induces a bijection of fundamental groups at `f (q, z)`. -/
theorem map_subtypeVal_compl_image_bijective (hf : IsOpenEmbedding f)
    (hZ : IsClosed (f '' {p | (p.2 : ℂ) = c})) (q : Q) (z : ↥(ball c R \ {c}))
    (h : hf.meridian q z = 1) :
    Function.Bijective (map (ContinuousMap.subtypeVal (f '' {p | (p.2 : ℂ) = c})ᶜ)
      (hf.restrictPuncturedBall (q, z))) := by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).1 ?_, map_subtypeVal_compl_image_surjective hf hZ q z⟩
  rw [ker_map_subtypeVal_compl_image_eq_normalClosure hf hZ q z, h,
    Subgroup.normalClosure_eq_bot_iff.2 subset_rfl]

/-- If the meridian class `hf.meridian q z` is trivial, the isomorphism
`π₁(X \ Z, f (q, z)) ≃* π₁(X, f (q, z))` induced by the inclusion, with `f`, `Q`, `X` and
`Z = f '' (Q × {c})` as in `ker_map_subtypeVal_compl_image_eq_normalClosure`. -/
noncomputable def complImageMulEquiv (hf : IsOpenEmbedding f)
    (hZ : IsClosed (f '' {p | (p.2 : ℂ) = c})) (q : Q) (z : ↥(ball c R \ {c}))
    (h : hf.meridian q z = 1) :
    FundamentalGroup (↥(f '' {p | (p.2 : ℂ) = c})ᶜ) (hf.restrictPuncturedBall (q, z)) ≃*
      FundamentalGroup X (hf.restrictPuncturedBall (q, z) : X) :=
  MulEquiv.ofBijective _ (map_subtypeVal_compl_image_bijective hf hZ q z h)

@[simp]
theorem complImageMulEquiv_apply (hf : IsOpenEmbedding f)
    (hZ : IsClosed (f '' {p | (p.2 : ℂ) = c})) (q : Q) (z : ↥(ball c R \ {c}))
    (h : hf.meridian q z = 1)
    (γ : FundamentalGroup (↥(f '' {p | (p.2 : ℂ) = c})ᶜ) (hf.restrictPuncturedBall (q, z))) :
    complImageMulEquiv hf hZ q z h γ =
      map (ContinuousMap.subtypeVal (f '' {p | (p.2 : ℂ) = c})ᶜ)
        (hf.restrictPuncturedBall (q, z)) γ :=
  (rfl)

end FundamentalGroup

end
